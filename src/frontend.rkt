#lang nanopass
(require racket/random)
(require nanopass/base)
(provide (all-defined-out))


;;Definición de Lenguaje Fuente
(define-language LF
  (terminals
   (variable (x))
   (primitive (pr))
   (constant (c))
   (list (l))
   (string (s))
   (type (t)))
   (Expr (e body)
         x
         pr
         c
         l
         s
         t
         (quot c)
         (primapp pr e* ...)
         (begin e* ... e)
         (if e0 e1)
         (if e0 e1 e2)
         (lambda ([x* t*]...) body* ... body)
         (let ([x* t* e*]...) body*  ... body)
         (letrec ([x* t* e*]...) body* ... body)
         (list e* ...)
         (e0 e1 ...)
         ;; agregadas por el proyecto
         (define x e)
         (while [e0] e1)
         (for [x e0] e1)
         ))


;; ========= Predicados ============================
(define (variable? x)
  (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x)
  (memq x '(+ - * / car cdr  length and not or < > equal? iszero? ++ --  equal-lst? empty? elem? append concat cons )))

(define (constant? x)
  (or (integer? x) (char? x) (boolean? x)))

;; ========= Tipos ==============================
;;Int |Char |Bool| Lambda |List | List of T | T -> T
(define (type? x) (or (b-type? x) (c-type? x)))

(define (b-type? x) (memq x '(Bool Char Int List Lambda)))

(define (c-type? x)
    (if (list? x)
        (let* ( [f (car x)] [s (cadr x)] [t (caddr x)])
            (or (and (equal? f 'List) (equal? s 'of) (type? t))
                (and (type? f) (equal? s '->) (type? t))))

        #f))

(define-parser parse-LF LF)





;; ================ PASSES =====================================




;;================== PASS 1 : remove-one-armed ===============

;;Lenguaje sin if's de una rama
(define-language L1
  (extends LF)
  (Expr (e body)
        (- (if e0 e1))))
(define-parser  parser-L1 L1)

;; definimos el pass
(define-pass remove-one-armed-if : LF (ir) -> L1()
  (Expr : Expr (ir) -> Expr()
        [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))




;;================== PASS 2 : remove-strings ===============

;; Define L2
;; Lenguaje que no tiene cadenas de texto sino listas de carecteres
(define-language L2
  (extends L1)
  (terminals
   (- (string (s))))
  (Expr (e body)
        (- s)))
(define-parser parse-L2 L2)

;; Pass that parse string as list of char
(define-pass remove-string : L1(ir) -> L2 ()
  (Expr : Expr (ir) -> Expr()
        [,s `(list ,(string->list s) ...)]))


;;================== PASS 3 : curry-let ===============

;;curry-let
;;Lenguaje que elimina (de L2) los let y letrec de múltiples párametros y los deja con un
;;solo parametro
(define-language L3
  (extends L2)
  (Expr (e body)
        (-
         (let ([x* t* e*] ...) body* ... body)
         (letrec ([x* t* e*] ...) body* ... body))
        (+
         (let ([x* t* e*]) body* ... body)
         (letrec ([x* t* e*]) body* ... body))
  )
)
(define-parser parse-L3 L3)


#|El proceso de currficación consite en
convertir una función de varios parametros
en una función de un solo:
add(x)-> \y=> x+y.
 La idea es curryficar let y letrec tal que
sus parametros adicionales se encuentren dentro  de otro let/letrec del body original  |#

(define-pass curry-let : L2(ir) -> L3() ;;Se le pasa como parametro el lenguaje de entrada junto con su argumento "ir" para especificar el lenguaje de entrada, y su lenguaje de Salida
  (Expr : Expr (ir) -> Expr()
       [(let ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body]) ;;Especificamos el cuerpo let de LF
        ;;Definimos f como el conjunto de valores de x* t* e*
        (let f ([paramsx* x*]
                 [paramst* t*]
                 [paramse* e*])
           (if(equal? (length paramsx*) 1) ;;Si solo hay un parametro en x devolvemos un let de L3  con la cabeza de toda la lista concatenada como parametro y su body original
           `(let ([,(car paramsx*),(car paramst*),(car paramse*)]) ,body* ...,body)
           `(let ([,(car paramsx*),(car paramst*),(car paramse*)]),(f (cdr paramsx*) (cdr paramst*) (cdr paramse*)));;En caso de que sean más parametros devolvemos un let de L3 con la cabeza de f y en el body pegaremos recursivamente un let con el siguiente paramentro y asi recursivamente hasta llegar hasta el 1er caso.
           ))
        ]
       [(letrec ([,x* ,t* ,[e*]] ...) ,[body*] ... ,[body]) ;;Especificamos el cuerpo let de LF
        ;;Definimos f como el conjunto de valores de x* t* e*
        (let f ([paramsx* x*]
                 [paramst* t*]
                 [paramse* e*])
           (if(equal? (length paramsx*) 1) ;;Si solo hay un parametro en x devolvemos un let de L3  con la cabeza de toda la lista concatenada como parametro y su body original
           `(letrec ([,(car paramsx*),(car paramst*),(car paramse*)]) ,body* ...,body)
           `(letrec ([,(car paramsx*),(car paramst*),(car paramse*)]),(f (cdr paramsx*) (cdr paramst*) (cdr paramse*)));;En caso de que sean más parametros devolvemos un let de L3 con la cabeza de f y en el body pegaremos recursivamente un let con el siguiente paramentro y asi recursivamente hasta llegar hasta el 1er caso.
           ))
        ]
))



;;================== PASS 4 : identify-assigments ===============

;;Función en el que los let que se identifiquen para definición de funciones se remplazan
;;con letrec
(define-pass identify-assigments : L3(ir) -> L3()
  (Expr : Expr (ir) -> Expr()
        [(let ([,x* ,t* ,[e*]]) ,[body*] ... ,[body])
         (if (eq? t* 'Lambda)
             `(letrec ([,x* ,t* ,e*]), body* ...,body)
              `(let ([,x*, t* ,e*] ), body* ...,body))] ) )


;;un-anonymous
;;Lenguaje encarcado de asignarle un identificador a funciones anónimas
(define-language L4
  (extends L3)
  (Expr (e body)
        (+ (letfun ([x* t* e*]) body*))))
(define-parser parse-L4 L4)


;;================== PASS 5 : un-anonymous ===============

(define foo-counter 0)
(define (generate-foo)
    (begin
    (set! foo-counter (+ 1 foo-counter))
    foo-counter ))


(define-pass un-anonymous : L3 (ir) -> L4 ()
       (Expr : Expr (ir) -> Expr()
             [(lambda ([,x* ,t*]...) ,[body*] ...,[body])
             (let ([fooaux (~v (generate-foo))]) (let ([foo (string->symbol (string-append "foo"fooaux) )])
           `(letfun ([,foo Lambda (lambda ([,x* ,t*] ...) ,body* ... ,body)]) ,foo)))]
        )
  )



;;================== PASS 6 : verift-arity ===============

;;verify-arity
;;Funcion auxiliar que verifica si la aridad del operador dado puede manejar el número de argumentos dados
(define (prc-ar pr actual)
  (match pr
    ; Los siguientes son operadores compatibles con cualquier numero de parametros
    ["+" #t]
    ["-" #t]
    ["*" #t]
    ["/" #t]
    ["or" #t]
    ["and" #t]
    ;; operaciones aritmeticas nuevas
    ["<" (eq? 2 actual)]
    [">" (eq? 2 actual)]
    ["iszero?" (eq? 1 actual)]
    ["equal?" (eq? 2 actual)]
    ["--" (eq? 1 actual)]
    ["++" (eq? 1 actual)]


    ;; Los siguientes son operadores de tipo lista, es decir solo aceptan 1 parametros
    ["not" (eq? 1 actual)]
    ["length" (eq? 1 actual)]
    ["car" (eq? 1 actual)]
    ["cdr" (eq? 1 actual)]
    ["equal-lst?" (eq? 1 actual)]
    ["empty?" (eq? 1 actual)]
    ;; estas operaciones de lista funcionan con dos parametros
    ["elem?" (eq? 2 actual)]
    ["concat" (eq? 2 actual)]
    ["cons" (eq? 2 actual)]

    ))
; Funcion que verifica si el numero de parametros corresponde con la aridad de las primitivas
(define-pass verify-arity : L4(ir)-> L4()
  (Expr : Expr (ir) -> Expr ()
        [(primapp ,pr ,[e*] ...)
         (if (prc-ar (symbol->string pr) (length e*))
             `(primapp ,pr ,e* ...)
             (error "Arity mismatch."))]))



;;================== PASS 7 : verift-vars ===============

;; definimos un ambiente global para la declaracion de variables
(define envG '())

;; Funcion auxiliar que limpia el ambiente global antes de hacer la verificacion de variables
(define (verify-vars e)
    (begin
    (set! envG '())
    (verify-vars-aux e)))

;;verify-vars-aux
;;Función que verificar que la expresión no tenga variables libres, de existir variables libres se regresa un error en otro caso devuelve
;;la expresión original
(define-pass verify-vars-aux : L4 (ir) -> L4 ()
  (Expr : Expr (ir [env null]) -> Expr ()
        [,x
         (if (or (memq x env) (memq x envG))
             x
             (error (string-append "Free variable " (symbol->string x))))]
        [(let ([,x ,t ,[e]]) ,[Expr : body* (cons x env) -> body*] ... ,[Expr : body (cons x env) -> body])
         `(let ([,x ,t ,e]) ,body* ... ,body)]
        [(letrec ([,x ,t ,[Expr : e (cons x env) -> e]]) ,[Expr : body* (cons x env) -> body*] ..., [Expr : body (cons x env) -> body])
         `(letrec ([,x ,t ,e]) ,body* ..., body)]
         ;; para las foo definidas
        [(letfun ([,x ,t ,[Expr : e (cons x env) -> e] ]) ,[Expr : body (cons x env) -> body])
         `(letfun ([,x ,t ,e]) ,body)]
        ;; para las lambda
        [(lambda ([,x* ,t*] ...) ,[Expr : body* (append x* env) -> body*] ... , [Expr : body (append x* env) -> body])
         `(lambda ([,x* ,t*] ...) ,body* ... ,body)]
         ;; caso para el for
        [(for [,x ,e0*] ,[Expr : e1 (cons x env) -> e1]  )
          `(for [,x ,e0*] ,e1)]
        [(define ,x ,[Expr : e (cons x env) -> e])
            (begin
            (set! envG (cons x envG))
            `(define ,x  ,e))]
        [(begin ,[e*] ,[e]) `(begin ,e* ,e) ]))


;; todos los procesos de front aplicados

(define (front-passes exp)
    (verify-vars (verify-arity (un-anonymous (identify-assigments ( curry-let (remove-string (remove-one-armed-if exp) ))))))  )