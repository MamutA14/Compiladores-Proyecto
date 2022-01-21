#|
Compiladores 2022-1  Proyecto Final 
Alumnos:
- Acosta Meza Alam
  No.cuenta : 315124569
- Arroyo Rivera Juan José
  No.cuenta: 416053223
- Sierra Casiano Vladimir
  No.cuenta: 316020361
|#

#lang nanopass
(require racket/random)
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
         (primapp pr e* ...)
         (define x e)
         (while [e0] e1)
         (for [x e0] e1)
         (quot c)
         (begin e* ... e)
         (if e0 e1)
         (if e0 e1 e2)
         (lambda ([x* t*]...) body* ... body)
         (let ([x* t* e*]...) body*  ... body)
         (letrec ([x* t* e*]...) body* ... body)
         (list e* ...)
         (e0 e1 ...)))

;;-----------Predicados--------------------------------------------
(define (variable? x)
  (and (symbol? x) (not (primitive? x)) (not (constant? x))))

(define (primitive? x)
  (memq x '(+ - * / car cdr  length and not or < > equal? iszero? ++ --)))

(define (constant? x)
  (or (integer? x) (char? x) (boolean? x)))

;;Tipos
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



;;---------------------------FRONT-END-------------------------
;;remove-one-armed
;;Lenguaje sin if's de una rama
(define-language L1
  (extends LF)
  (Expr (e body)
        (- (if e0 e1))))
(define-parser  parser-L1 L1)

(define-pass remove-one-armed-if : LF (ir) -> L1()
  (Expr : Expr (ir) -> Expr()
        [(if ,[e0] ,[e1]) `(if ,e0 ,e1 (void))]))


;; remove-string
; Lenguaje que no tiene cadenas de texto sino listas de carecteres
(define-language L2
  (extends L1)
  (terminals
   (- (string (s))))
  (Expr (e body)
        (- s)))
(define-parser parse-L2 L2)


(define-pass remove-string : L1(ir) -> L2 ()
  (Expr : Expr (ir) -> Expr()
        [,s `(list ,(string->list s) ...)]))

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

;;identify-assigments
;;Función en el que los let que se identifiquen para definición de funciones se remplazan
;;con letrec
(define-pass identify-assigments : L3(ir) -> L3()
  (Expr : Expr (ir) -> Expr()
        [(let ([,x* ,t* ,[e*]]) ,[body*] ... ,[body])
         (if (eq? t* 'Lambda)
             `(letrec ([,x* ,t* ,e*]), body* ...,body)
              `(let ([,x*, t* ,e*] ), body* ...,body))]
  )
)

;;un-anonymous
;;Lenguaje encarcado de asignarle un identificador a funciones anónimas
(define-language L4
  (extends L3)
  (Expr (e body)        
        (+ (letfun ([x* t* e*]) body*))))
(define-parser parse-L4 L4)


(define-pass un-anonymous : L3 (ir) -> L4 ()
  (definitions
    ;;Función auxiliar que va a  generar una cadena aleatoria oscilando entre un tamaño entre 3 y 7 
    (define (generate-random-string)
      ;;Tamaño de la cadena
      (let ([len (random 3 7)]) 
        (define bs
          ;;Se divide entre dos el tamaño de  la cadena ya que sera la base en el que se trabajara
          (quotient
           (if (odd? len)
               (add1 len)
               len)
           2))
        (define str
          (with-output-to-string ;;Permitira devolver el resultado al llamar a la función de la forma str 
            (lambda ()
              (for ([b (in-bytes (crypto-random-bytes bs ))]);;Iterara por una lista de números aleatorios del tamaño de la mitad de la cadena
                (when (< b 16)
                  (display "0")) ;; Si es número menor a la base 16 entonces se concatena un 0
                  (display (number->string b 16))
          )))) ;; Se imprimira un número en base 16 y se concatenara con todos los demás 
        (if (odd? len)
            (substring str 0 len);;Como la cadena es mayor por un índice extra se toma la subcadena de 0, len
            str))
       ))
       (Expr : Expr (ir) -> Expr()
             [(lambda ([,x* ,t*]...) ,[body*] ...,[body])
             (let ([fooaux (generate-random-string)]) (let ([foo (string->symbol (string-append "f"fooaux) )])
           `(letfun ([,foo Lambda (lambda ([,x* ,t*] ...) ,body* ... ,body)]) ,foo)))]
        )
  )
;;verify-arity
;;Funcion auxiliar que verifica si la aridad del operador dado puede manejar el número de argumentos dados
(define (prc-ar pr actual)
  (match pr
    ; Los siguientes son operadores compatibles con cualquier numero de parametros
    ["+" #t]
    ["-" #t]
    ["/" #t]
    ;; Los siguientes son operadores de tipo lista, es decir solo aceptan 1 parametros
    ["length" (eq? 1 actual)]
    ["car" (eq? 1 actual)]
    ["cdr" (eq? 1 actual)]))
; Funcion que verifica si el numero de parametros corresponde con la aridad de las primitivas
(define-pass verify-arity : L4(ir)-> L4()
  (Expr : Expr (ir) -> Expr ()
        [(primapp ,pr ,[e*] ...)
         (if (prc-ar (symbol->string pr) (length e*))
             `(primapp ,pr ,e* ...)
             (error "Arity mismatch."))]))


;;verify-vars
;;Función que verificar que la expresión no tenga variables libres, de existir variables libres se regresa un error en otro caso devuelve
;;la expresión original
(define-pass verify-vars : L4 (ir) -> L4 ()
  (Expr : Expr (ir [env null]) -> Expr ()
        [,x
         (if (memq x env)
             x
             (error (string-append "Free variable " (symbol->string x))))]
        [(let ([,x ,t ,[e]]) ,[Expr : body* (cons x env) -> body*] ... ,[Expr : body (cons x env) -> body])
         `(let ([,x ,t ,e]) ,body* ... ,body)]
        [(letrec ([,x ,t ,[Expr : e (cons x env) -> e]]) ,[Expr : body* (cons x env) -> body*] ..., [Expr : body (cons x env) -> body])
         `(letrec ([,x ,t ,e]) ,body* ..., body)]
        [(lambda ([,x* ,t*] ...) ,[Expr : body* (append x* env) -> body*] ... , [Expr : body (append x* env) -> body])
         `(lambda ([,x* ,t*] ...) ,body* ... ,body)]))


;;---------------------------MIDDLE-END-------------------------
;;curry
;;Lenguaje que se encargara de currificar las expresiones: lambdas, aplicaciones de función 
(define-language L5
  (extends L4)
  (Expr (e body)
        (-
         (lambda ([x* t* ] ...) body* ... body)
         (e0 e1 ...)
         )
        (+
         (lambda ([x t ]) body* ... body)
         (e0 e1))
  )
)
(define-parser parse-L5 L5)
(define-pass curry : L4(ir) -> L5()
  (Expr : Expr(ir) -> Expr()
        [(lambda ([,x*,t*]...),[body*] ... ,[body])
         ;;Definimos f como el conjunto de valores de x* t* 
         (let f ([paramsx* x*]
                 [paramst* t*])
           (if (equal? (length paramsx*) 1)
               `(lambda ([,(car paramsx*),(car paramst*)]) ,body* ...,body)
               `(lambda ([,(car paramsx*),(car paramst*)]),(f (cdr paramsx*) (cdr paramst*)))
               ))]
        [(,[e0],[e1]  ...)
         (let f ([paramse0 e0]
                 [paramse1 e1])
           (if (equal? (length paramse1 ) 0) 
               `,paramse0
               (f `(, paramse0 ,(car paramse1)) (cdr paramse1))
               ))]))


;;type-const
(define-language L6
  (extends L5)
  (Expr (e body)
        (-
         (quot c)
         )
        (+
         (const t c)
         )
  )
)
(define-parser parse-L6 L6)
(define-pass type-const : L5(ir) -> L6()
  (Expr : Expr(ir) -> Expr()
        [(quot , c) ;;(begin ,[e*] ... ,[e])
         (cond
           [(number? c) `(const , 'Int , c) ]
           [(boolean? c) `(const , 'Bool , c) ]
           [else `(const , 'Char , c) ])
        ])
   )