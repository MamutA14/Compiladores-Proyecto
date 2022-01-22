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
(require nanopass/base)
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


;;Type-infer
;;Definiciones auxiliares
(define (unify t1 t2)
    (if (and (type? t1) (type? t2))
        (cond
            [(equal? t1 t2) #t]
            [(and (equal? 'List t1) (list? t2))  (equal? (car t2) 'List) ]
            [(and (equal? 'List t2) (list? t1))  (equal? (car t1) 'List) ]
            [(and (list? t1) (list? t2)) (and (unify (car t1) (car t2)))]
            [else #f])
        (error "Se esperaban 2 tipos")))

;; Unas funciones auxiliares para realizar la busqueda de variables en el ambiente
(define (find-type x env)
    (cond
        [(empty? env) (error "Error, variable no esta en el ambiente")]
        [(eq? (caar env) x) (cadar env)] ;; caso cuando el ambiente tiene la forma '( (x t) ... ) , devolvemos t
        [else (find-type x (cdr env))] ))  ;; llamada recursiva sobre el resto del ambiente si no coincide

;; Funcion que dada una variable x, un tipo t y un ambiente env devuelve un nuevo ambiente
;; resultado de agregar la tupla (x,t) al ambiente
(define (add-var-to-env x t env)
    (list (list x t) env))

(define (J e env)
    (nanopass-case (L6 Expr) e
        [,x  (find-type x env)]         ;; para variables buscamos directamente en el ambiente

        [(const ,t ,c ) t]              ;; para constantes tenemos el tipo especificado en el const

        [(begin ,e* ... ,e) (J e env)]   ;; Retornamos el tipo de la ultima exprexion

        [(primapp ,pr ,e* ...)
            (if (check-args-types pr  (map (lambda (x) (J x env)) e*) )
                (case pr
                    [(+ - * / length) 'Int]
                    [(car) (caddr (car  (map (lambda (x) (J x env)) e*)))]
                    [(cdr) (car  (map (lambda (x) (J x env)) e*) )])
                (error 'J "Los tipos de ~a no son compatbles para la operacion ~a" e* pr))]

        ;; Para el if verificamos que el tipo de e0 sea Bool, y los tipos de e1 y e2 sean los mismos
        [(if ,e0 ,e1 ,e2)
            (if (and (equal?  (J e0 env) 'Bool)  (unify (J e1 env) (J e2 env)))
                (J e1 env)
                (error 'J "El tipo de ~a debe ser Bool. Y el tipo de ~a debe ser igual al de ~a " e0 e1 e2) )]

        ;; Para las lambdas el tipo es t -> type_of_body
        [(lambda ([,x ,t]) ,body)  (list t '->  (J body (add-var-to-env x t env)))]

        ;; para expresiones let devolvemos el tipo del body agregando (x t) al ambiente
        [(let ([,x ,t ,e]) ,body)
            (if  (unify t (J e env))
                (J body (add-var-to-env x t env))
                ;; hay un error si el tipo de e no coincide con t
                (error 'J "El tipo de ~a no coincide con el de la expresion ~a." x e) )]

        ;; para expresiones letrec devolvemos el tipo del body agregando (x t) al ambiente
        [(letrec ([,x ,t ,e]) ,body)
            (if  (unify t (J e (add-var-to-env x t env)))
                (J body (add-var-to-env x t env))
                ;; hay un error si el tipo de e no coincide con t
                (error 'J "El tipo de ~a no coincide con el de la expresion ~a." x e) )]

        ;; Para expresiones letrec devolvemos el tipo del body agregando (x t) al ambiente
        [(letfun ([,x ,t ,e]) ,body)
            (if  (and (equal? '-> (cadr t)) (unify t (J e env)) )
                (J body (add-var-to-env x t env))
                ;; hay un error si el tipo de e no coincide con t
                (error 'J "El tipo de ~a no coincide con el de la expresion ~a." x e) )]

        [(list ,e* ...)
            ;; si es la lista vacia devoldemos List
            (if (empty? e*)
                'List
                ;; Calculamos los tipos de los elementos
                (let* ([types (map (lambda (x) (J x env)) e*) ]
                        [t1 (car types)])
                    ;; Si todos los mismos son los mismos deovlvemos List of T1
                    (if (andmap (lambda (x) (unify x t1)) types)
                        (list 'List 'of t1)
                        (error 'J "Los elementos de la lista ~a no son del mismo tipo." e*)))  )]

        [(,e0 ,e1)
            (let ([t0 (J e0 env)] [t1 (J e1 env)])
                (if (and (list? t0) (equal? (cadr t0) '->) (unify (car t0) t1))  ;; verificamos que el tipo de e0 sea T1->T2 y el de e1 sea T1
                    (caddr t0)                                                   ;; Al aplicar la funcion se devuelve T2
                    (error 'J "El tipo de ~a no es compatible con el de ~a  para realizar la aplicacion de funcion." e0 e1) )  )]
  ))


;; Funcion que verifica que dada una lista de tipos args, estos tipos sean los correctos para la operacion pr
(define (check-args-types pr args )
    (case pr
        [(+ - * /) (andmap (lambda (x) (equal? x 'Int)) args) ]  ;; Estas primitivas son sobre enteros
        [(car cdr length) (andmap (lambda (x) (and (list? x) (equal? (car x) 'List))) args) ] ))  ;; Estas operaciones van sobre listas


(define-pass type-infer : L6(ir) -> L6()
    (Expr : Expr (ir) -> Expr ()
        ;; Para let solo inferimos el tipo de t cuando de entrada es List, lo denombra a List of
        [(let ([,x ,t ,[e]]) ,[body])
            (case t
                [(List) `(let ([,x ,(J e '()) ,e]) ,body) ]
                [else   `(let ([,x ,t ,e]) ,body) ])]
        ;; Para letrec solo inferimos el tipo de t cuando de entrada es Lambda o List, los cambia de T->T y List of respectivamente.
        [(letrec ([,x ,t ,[e]]) ,[body])
            (let ( [fixed-type (case t [(List Lambda) (J e '())] [else t]) ])
                `(letrec ([,x ,fixed-type ,e]) ,body)
            )]
        ;; Para letfun siempre inferimos el tipo de t, aplicando tanto para List como para Lambda
        [(letfun ([,x ,t ,[e]]) ,[body])
            `(letfun ([,x ,(J e '()) ,e]) ,body)]  ))






;;uncurry
;;Lenguaje que descurrifica las funciones anonimas
(define-language L7
    (extends L6)
    (Expr (e body)
          (- (lambda ([x t ]) body* ... body))
          (+ (lambda ([x* t*] ...) body))))

(define-parser parse-L7 L7)


;; Definimos un pass auxiliar para identificar lambdas
(define-pass lambda? : (L6 Expr) (e) -> * (bool)
    (Expr : Expr (e) -> * (bool)
        [(lambda ([,x ,t]) ,body) #t]
        [else #f])
    (Expr e))

;; Funcion auxiliar que devuelve el body de una expresion lambda
(define (get-body-lambda expr)
    (nanopass-case (L6 Expr) expr
        [(lambda ([,x ,t]) ,body) (get-body-lambda body)]
        [else expr]))

;; Funcion auxiliar para obtener la lista de asignaciones que se hacen en una expression lambda dada
(define (get-assigments-lambda expr acum)
    (nanopass-case (L6 Expr) expr
        [(lambda ([,x ,t]) ,body)  (append (list (list x t)) (get-assigments-lambda body acum)) ]
        [else acum]))


(define (uncurry-aux expr)
    (nanopass-case (L6 Expr) expr
        [(lambda ([,x ,t]) ,body)
            (parse-L7 `(lambda ,(get-assigments-lambda expr '()) ,(unparse-L7 (uncurry-aux (get-body-lambda expr)))))]
        [(let ([,x ,t ,[e]]) ,[body])
            (with-output-language (L7 Expr) `(let ([,x ,t ,e]) ,body))]
        [(letrec ([,x ,t ,[e]]) ,[body])
            (with-output-language (L7 Expr) `(letrec ([,x ,t ,e]) ,body))]
        [(letfun ([,x ,t ,[e]]) ,[body])
            (with-output-language (L7 Expr) `(letfun ([,x ,t ,e]) ,body))]
        [(begin ,[e*] ... ,[e])
            (with-output-language (L7 Expr) `(begin ,e* ... ,e))]
        [(primapp ,pr ,[e*] ...)
            (with-output-language (L7 Expr) `(primapp ,pr ,e* ...))]
        [(if ,[e0] ,[e1] ,[e2])
            (with-output-language (L7 Expr) `(if ,e0 ,e1 ,e2))]
        [(const ,t ,c)
            (with-output-language (L7 Expr) `(const ,t ,c))]
        [(list ,[e*] ...)
            (with-output-language (L7 Expr) `(list ,e* ...))]
        [(,[e0] ,[e1])
            (with-output-language (L7 Expr) `(,e0 ,e1))]
        [else (parse-L7 (unparse-L6 expr))] ))


(define-pass uncurry : L6 (ir) -> L7 ()
    (Expr : Expr (ir) -> Expr ())
        (uncurry-aux ir))

;;---------------------------BACK-END-------------------------


;;assigment
;;Funciones auxiliares

(define (symbol-table-var-aux expr table)
    (nanopass-case (L7 Expr) expr
        [(let ([,x ,t ,[e] ]) ,body)
            (begin (hash-set! table x (cons t e))
                    (symbol-table-var-aux body table))]
        [(letrec ([,x ,t ,e]) ,body)
            (begin (hash-set! (symbol-table-var-aux body table) x (cons t e))
                    (symbol-table-var-aux body table))]
        [(letfun ([,x ,t ,e]) ,body)
            (begin (hash-set! table x (cons t e))
                    (symbol-table-var-aux body table))]
        [(,e0 ,e1)
            (begin
                (define h1 table)
                (set! h1 (symbol-table-var-aux e1 h1))
                (define h2 h1)
                (set! h2 (symbol-table-var-aux e1 h2))
                h2)]
        [(primapp ,pr ,[e*] ...)
            (let f ([e* e*]) (if (null? e*) table (symbol-table-var-aux (first e*) (f (rest e*)))))]
        [(begin ,e* ... ,e)
            (begin (map (lambda (e) (symbol-table-var-aux e table)) e*))]
        [(if ,e0 ,e1 ,e2)
            (begin
                (symbol-table-var-aux e0 table)
                (symbol-table-var-aux e1 table)
                (symbol-table-var-aux e2 table))]
        [(lambda ([,x* ,t*] ...) ,body) (symbol-table-var-aux body table)]
        [(list ,e* ... ,e)
            (begin (map (lambda (e) (symbol-table-var-aux e table)) e*) (symbol-table-var-aux e table))]
        [else table] ))

;; Funcion que genera la tabla de simbolos de una expresión
(define (symbol-table-var expr)
    (nanopass-case (L7 Expr) expr
                    [else (symbol-table-var-aux expr (make-hash))]))



;;Lenguaje que modifica los constructores de let, letrec, letfun
;;eliminando el valor asociado a los identificadores y el tipo correspondiente
(define-language L8
  (extends L7)
  (Expr (e body)
        (- (let ([x* t* e*]) body* ... body)
           (letrec ([x* t* e*]) body* ... body)
           (letfun ([x* t* e*]) body*))
        (+ (let x body)
           (letrec x body)
           (letfun x body))))

(define-parser parse-L8 L8)

(define-pass assigment : L7 (ir) -> L8 (hash)
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,[body]) `(let ,x ,body)]
        [(letrec ([,x ,t ,e]) ,[body]) `(letrec ,x ,body)]
        [(letrec ([,x ,t ,e]) ,[body]) `(letfun ,x ,body)])
  (values (Expr ir) (symbol-table-var ir)))


;; list-to-array

; Funcion auxiliar que dada una lista toma el primer elemento y aplica sobre ese elemento el algoritmo J
(define (J-aux x)
    (nanopass-case (L8 Expr) x
        [(list ,e* ... ,e) (J e '())] ))
;; Lenguaje que servira en traducir listas (no vacias) en arreglos
(define-language L9
    (extends L8)
    (Expr (e body)
        (- (list e* ...))
        (+ (array c t [e* ...]))))
(define-parser parse-L9 L9)

(define-pass list-to-array : L8 (ir) -> L9 ()
 (Expr : Expr (ir) -> Expr()
    [ (list ,[e*] ...)
        (let ([t (J-aux ir)])
        `(array ,(length e*)  ,t  [,e* ...] )) ] ))