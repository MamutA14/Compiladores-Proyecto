#lang nanopass

(require "frontend.rkt")
(provide (all-defined-out))


;;================== PASS 8 : curry ===============


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
         (e0 e1))  ))

(define-parser parse-L5 L5)

(define-pass curry : L4(ir) -> L5()
  (Expr : Expr(ir) -> Expr()
        [(lambda ([,x*,t*]...),[body*] ... ,[body])
         ;;Definimos f como el conjunto de valores de x* t*
         (let f ([paramsx* x*]
                 [paramst* t*])
           (if (equal? (length paramsx*) 1)
               `(lambda ([,(car paramsx*),(car paramst*)]) ,body* ...,body)
               `(lambda ([,(car paramsx*),(car paramst*)]),(f (cdr paramsx*) (cdr paramst*))) ))]
        [(,[e0],[e1]  ...)
         (let f ([paramse0 e0]
                 [paramse1 e1])
           (if (equal? (length paramse1 ) 0)
               `,paramse0
               (f `(, paramse0 ,(car paramse1)) (cdr paramse1)) ))]) )






;;================== PASS 9 : type-const ===============


;; New language, remove quot constrcutor and add const
(define-language L6
  (extends L5)
  (Expr (e body)
        (-
         (quot c)
         )
        (+
         (const t c)
         ) ) )


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




;;================== PASS 10 : type-infer  ===============

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
        [(empty? env) (error 'find-type "Error, variable ~a no esta en el ambiente" x)]
        [(eq? (caar env) x) (cadar env)] ;; caso cuando el ambiente tiene la forma '( (x t) ... ) , devolvemos t
        [else (find-type x (cdr env))] ))  ;; llamada recursiva sobre el resto del ambiente si no coincide


;; Funcion que dada una variable x, un tipo t y un ambiente env devuelve un nuevo ambiente
;; resultado de agregar la tupla (x,t) al ambiente
(define (add-var-to-env x t env)
    (list (list x t) env))

;; Funcion que verifica que dada una lista de tipos args, estos tipos sean los correctos para la operacion pr
(define (check-args-types pr args )
    (case pr
        [(+ - * / < > equal? iszero? ++ --) (andmap (lambda (x) (equal? x 'Int)) args) ]  ;; Estas primitivas son sobre enteros
        [(append cons)  (let ([tipo_e (car args)])  (equal? tipo_e (car (cddadr args) )) )]
        [(concat) (let ([type (car args)])  (andmap (lambda (x) (equal? x type)) args) )]
        [(elem?) (ormap (lambda (x) (and (list? x) (equal? (car x) 'List))) args) ]  ;; Estas operaciones van sobre listas
        [(car cdr length equal-lst? empty?) (andmap (lambda (x) (and (list? x) (equal? (car x) 'List))) args) ] ))  ;; Estas operaciones van sobre listas


(define global-env-J '())
(define (add-to-global-J x t )
    (set! global-env-J (append (cons (list x t) '()) global-env-J))
)
(define (J e env)
    (nanopass-case (L6 Expr) e
        [,x  (find-type x (append env global-env-J))]         ;; para variables buscamos directamente en el ambiente

       [(define ,x ,e)
            (let ([tipo (J e env)])
            (begin
            (set! global-env-J (add-var-to-env x tipo global-env-J))
            tipo) )]

        [(const ,t ,c ) t]              ;; para constantes tenemos el tipo especificado en el const

        [(begin ,e* ... ,e)
            (begin
            (for ([i e*]) (J i env))
            (J e env))]   ;; Retornamos el tipo de la ultima exprexion

        [(primapp ,pr ,e* ...)
            (let ([tipos  (map (lambda (x) (J x env)) e*)] )
            (if (check-args-types pr tipos)
                (case pr
                    [(+ - * / ++ -- length) 'Int]
                    [(< > equal? iszero? equal-lst? empty? elem?) 'Bool]
                    [(concat) (car tipos)]
                    [(cons append) (cadr tipos)]
                    [(car) (caddr (car  (map (lambda (x) (J x env)) e*)))]
                    [(cdr) (car  (map (lambda (x) (J x env)) e*) )])
                (error 'J "Los tipos de ~a no son compatbles para la operacion ~a" e* pr)) )]

        ;; Para el if verificamos que el tipo de e0 sea Bool, y los tipos de e1 y e2 sean los mismos
        [(if ,e0 ,e1 ,e2)
            (if (and (equal?  (J e0 env) 'Bool)  (unify (J e1 env) (J e2 env)))
                (J e1 env)
                (error 'J "El tipo de ~a debe ser Bool. Y el tipo de ~a debe ser igual al de ~a " e0 e1 e2) )]

        ;; Para las lambdas el tipo es t -> type_of_body
        [(lambda ([,x ,t]) ,body)
         (begin
         (add-to-global-J x t)
         (list t '->  (J body (add-var-to-env x t env))) )]

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
                (let ([tipo (J e env)])
            ;; (if  (and (equal? '-> (cadr t)) (unify t (J e env)) )
                (J body (add-var-to-env x tipo env)))]
                ;; hay un error si el tipo de e no coincide con t
               ;; (error 'J "El tipo de ~a no coincide con el de la expresion ~a." x e) )]

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
        [(while [,[e0]] ,e1) (J e1 env)]
        [(for [,x ,[e0]] ,e1)  (J e1 (add-var-to-env x (caddr e0) env)) ]
  ))

(define (apply-J e)
    (begin
        (set! global-env-J '())
        (J e ' ()) ) )


(define-pass type-infer : L6(ir) -> L6()
    (Expr : Expr (ir) -> Expr ()
        ;; Para let solo inferimos el tipo de t cuando de entrada es List, lo denombra a List of
        [(let ([,x ,t ,[e]]) ,[body])
            (case t
                [(List) `(let ([,x ,(apply-J e ) ,e]) ,body) ]
                [else   `(let ([,x ,t ,e]) ,body) ])]
        ;; Para letrec solo inferimos el tipo de t cuando de entrada es Lambda o List, los cambia de T->T y List of respectivamente.
        [(letrec ([,x ,t ,[e]]) ,[body])
            (let ( [fixed-type (case t [(List Lambda) (apply-J e )] [else t]) ])
                `(letrec ([,x ,fixed-type ,e]) ,body) )]
        ;; Para letfun siempre inferimos el tipo de t, aplicando tanto para List como para Lambda
        [(letfun ([,x ,t ,[e]]) ,[body])
            `(letfun ([,x ,(apply-J e) ,e]) ,body)]  ))





;;================== PASS 11 : uncurry ===============



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

;; Pass that uncurryfies lambda expressions from L10.



