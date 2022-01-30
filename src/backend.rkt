#lang nanopass

(require "frontend.rkt")
(require "middle.rkt")
(provide (all-defined-out))


;;================== PASS 12 : assigment ===============
(define (symbol-table-var-aux expr table)
    (nanopass-case (L7 Expr) expr
        [(define ,x ,t ,e)
            (begin
            (hash-set! table x (cons t  e))
             table)]
        [(let ([,x ,t ,e ]) ,body)
            (begin (hash-set! table x (cons t e) )
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
            (begin
                (map (lambda (x) (symbol-table-var-aux x table)) e*)
                (symbol-table-var-aux e table) )]
        [(if ,e0 ,e1 ,e2)
            (begin
                (symbol-table-var-aux e0 table)
                (symbol-table-var-aux e1 table)
                (symbol-table-var-aux e2 table))]
        [(lambda ([,x* ,t*] ...) ,body) (symbol-table-var-aux body table)]
        [(list ,e* ... ,e)
            (begin (map (lambda (e) (symbol-table-var-aux e table)) e*) (symbol-table-var-aux e table))]
        [(while [,[e0]] ,e1)
            (begin
                (symbol-table-var-aux e0 table)
                (symbol-table-var-aux e1 table) )]
        [(for [,x ,[e0]] ,e1)  (symbol-table-var-aux e1 table) ]
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

(define-pass assigment-aux : L7 (ir) -> L8 (hash)
  (Expr : Expr (ir) -> Expr ()
        [(let ([,x ,t ,e]) ,[body]) `(let ,x ,body)]
        [(letrec ([,x ,t ,e]) ,[body]) `(letrec ,x ,body)]
        [(letfun ([,x ,t ,e]) ,[body]) `(letfun ,x ,body)])
  (values (Expr ir) (symbol-table-var ir)))

(define (assigment e)
    (define-values (assigment-exp assigment-hash)
        (assigment-aux e)
    )
    (list assigment-exp assigment-hash)
 )

;;================== PASS 13 : list-to-array ===============


;; Lenguaje que servira en traducir listas (no vacias) en arreglos
(define-language L9
    (extends L8)
    (Expr (e body)
        (- (list e* ...))
        (+ (array c t [e* ...]))))

(define-parser parse-L9 L9)


; Funcion auxiliar que dada una lista toma el primer elemento y aplica sobre ese elemento el algoritmo J


(define global-env-JL8 '())

(define (J-forL8-aux x s-table)
    (nanopass-case (L8 Expr) x
        [(list ,e* ... ,e) (J-forL8 e s-table)] ))

(define-pass list-to-array-aux : L8 (ir g-hash) -> L9 ()
 (Expr : Expr (ir) -> Expr()
    [ (list ,[e*] ...)
        (let ([t (J-forL8-aux ir g-hash)])
        `(array ,(length e*)  ,t  [,e* ...] )) ] ))

(define (list-to-array exp-hash)
    (begin
        (set! global-env-JL8 '())
    (let* ([exp (car exp-hash)]
            [hash-t (cadr exp-hash)])
        (list (list-to-array-aux exp exp-hash) hash-t)
    ))
 )



(define (add-to-global-JL8 x t )
    (set! global-env-JL8 (append (cons (list x t) '()) global-env-JL8))
)

(define (J-forL8 e env)
    (nanopass-case (L8 Expr) e
       [,x  (find-type x (append env global-env-JL8))]         ;; para variables buscamos directamente en el ambiente

       [(define ,x ,t ,e)
            (let ([tipo (J-forL8 e env)])
            (begin
            (set! global-env-JL8 (add-var-to-env x tipo global-env-JL8))
            tipo) )]

        [(const ,t ,c ) t]              ;; para constantes tenemos el tipo especificado en el const

        [(begin ,e* ... ,e)
            (begin
            (for ([i e*]) (J-forL8 i env))
            (J-forL8 e env))]   ;; Retornamos el tipo de la ultima exprexion

        [(primapp ,pr ,e* ...)
            (let ([tipos  (map (lambda (x) (J-forL8 x env)) e*)] )
            (if (check-args-types pr tipos)
                (case pr
                    [(+ - * / ++ -- length) 'Int]
                    [(< > equal? iszero? equal-lst? empty? elem? and or not) 'Bool]
                    [(concat) (car tipos)]
                    [(cons append) (cadr tipos)]
                    [(car) (caddr (car  (map (lambda (x) (J x env)) e*)))]
                    [(cdr) (car  (map (lambda (x) (J x env)) e*) )])
                (error 'J-forL8 "Los tipos de ~a no son compatbles para la operacion ~a" e* pr)) )]

        ;; Para el if verificamos que el tipo de e0 sea Bool, y los tipos de e1 y e2 sean los mismos
        [(if ,e0 ,e1 ,e2)
            (if (and (equal?  (J-forL8 e0 env) 'Bool)  (unify (J-forL8 e1 env) (J-forL8 e2 env)))
                (J-forL8 e1 env)
                (error 'J-forL8 "El tipo de ~a debe ser Bool. Y el tipo de ~a debe ser igual al de ~a " e0 e1 e2) )]

        ;; Para las lambdas el tipo es t -> type_of_body
        [(lambda ([,x ,t]) ,body)
         (begin
         (add-to-global-JL8 x t)
         (list t '->  (J-forL8 body (add-var-to-env x t env))) )]

        ;; para expresiones let devolvemos el tipo del body , los tipos de x estan en la tabla de simbolos
        [(let ,x ,body)
                (J-forL8 body env)]
        [(letrec ,x ,body)
                (J-forL8 body env)]
        [(letfun ,x ,body)
                (J-forL8 body env)]


        [(list ,e* ...)
            ;; si es la lista vacia devoldemos List
            (if (empty? e*)
                'List
                ;; Calculamos los tipos de los elementos
                (let* ([types (map (lambda (x) (J-forL8 x env)) e*) ]
                        [t1 (car types)])
                    ;; Si todos los mismos son los mismos deovlvemos List of T1
                    (if (andmap (lambda (x) (unify x t1)) types)
                        (list 'List 'of t1)
                        (error 'J-forL8 "Los elementos de la lista ~a no son del mismo tipo." e*)))  )]

        [(,e0 ,e1)
            (let ([t0 (J-forL8 e0 env)] [t1 (J-forL8 e1 env)])
                (if (and (list? t0) (equal? (cadr t0) '->) (unify (car t0) t1))  ;; verificamos que el tipo de e0 sea T1->T2 y el de e1 sea T1
                    (caddr t0)                                                   ;; Al aplicar la funcion se devuelve T2
                    (error 'J-forL8 "El tipo de ~a no es compatible con el de ~a  para realizar la aplicacion de funcion." e0 e1) )  )]
        [(while [,[e0]] ,e1) (J-forL8 e1 env)]
        [(for [,x ,[e0]] ,e1)  (J-forL8 e1 (add-var-to-env x (caddr e0) env)) ] ))




;;Función auxiliar que extrae elementos de un arreglo
;;(define (extract-array e)
 ;; (nanopass-case (L9 Expr) e
   ;;              [(array ,len ,t (,e* ...)) (list len t e*)]))



;==================== Función c ================================

(define (c exp-table)
    (let* ([exp (car exp-table)]
            [tabla (cadr exp-table)])
        (c-aux exp tabla) ))

(define (remove-quote s)
    (list->string (filter (lambda (x) (not (eq? x #\'))) (string->list s))))

(define (add-semicolon-if-needed x)
    (if (eq? (last (string->list x)) #\;)
      x
      (string-append x ";"))
)
(define (c-aux expr tabla)
  (nanopass-case
   (L9 Expr) expr
   [(define ,x ,t ,e)
        (let* ([tipo (c-aux t tabla)]
                [es (c-aux e tabla)])
            (string-append tipo " " (remove-quote (~v x)) " = " es ";")
        )
   ]
   [(const ,t ,c)
    (match t
           ['Int (number->string c)]
           ['Bool (match c
                  ['#t "1"]
                  ['#f "0"])]
           ['Char (string c)])]
   [,t
       (match t
       ['Int  "int"]
       ['Bool  "int"]
       ['Char  "char"]
       )]
   ;; para el while creaoms el bloque de codigos
   [(while [,e0] ,e1) (string-append "while (" (c-aux e0 tabla) ")" "{\n    " (add-semicolon-if-needed (c-aux e1 tabla)) "\n}")]

   [(for [,x ,e0] ,e1)
     (let* ([d (list-to-array (parse-L8 e0))]
            [size (first d)]
            [t (second d)]
            [e* (third e0)])
       (string-append "for(" (c-aux t tabla) " " (c-aux x tabla) "=0; i < " (number->string size) ";i++){\n" (c-aux e1 tabla) "\n}"))]
   [,x (symbol->string x)]
   [(primapp ,pr ,e* ...)
    (match pr
      ['+ (string-append (c-aux (first e*) tabla) "+" (c-aux (second e*) tabla))]
      ['- (string-append (c-aux (first e*) tabla) "-" (c-aux (second e*) tabla))]
      ['/ (string-append (c-aux (first e*) tabla) "/" (c-aux (second e*) tabla))]
      ['* (string-append (c-aux (first e*) tabla) "*" (c-aux (second e*) tabla))]
      ['< (string-append (c-aux (first e*) tabla) "<" (c-aux (second e*) tabla))]
      ['> (string-append (c-aux (first e*) tabla) ">" (c-aux (second e*) tabla))]
      ['equal? (string-append (c-aux (first e*) tabla) "==" (c-aux (second e*) tabla))]
      ['iszero? (string-append "(" (c-aux (first e*) tabla) "==0)")]
      ['++ (string-append  (c-aux (first e*) tabla) "++;" )]
      ['-- (string-append  (c-aux (first e*) tabla) "--;" )]
      ['and (string-append (c-aux (first e*) tabla) "&&" (c-aux (second e*) tabla))]
      ['or (string-append  (c-aux (first e*) tabla) "||" (c-aux (second e*) tabla))]
      ['not ("!" (string-append (c-aux (first e*) tabla)))]
      ['car (let ([e (first e*)]) (string-append (c-aux e tabla) "[0]"))]
      ['length (let ([e (first e*)])
                (string-append "sizeof(" (c-aux e tabla) ")/sizeof(" (c-aux (parse-L9 `(car e)) tabla) ")"))]

      ['cdr (let ([e (first e*)] [len (c-aux (parse-L9 `(primapp length e)) tabla)]) ;;Se considera el caso como si fuera una pila se va quitando el 1er elemento y se queda con la cola
            (string-append "for(i=1; i<" len "; i++){\n"
                                    (c-aux e tabla) "[i]=" (c-aux e tabla) "[i+1];" "\n
                                      
                            }" ))])]
     [(array ,c0 ,t [,e* ...])  
       (string-append
                   (symbol->string t) (string #\space) (string-append "arr" (number->string (~v (generate-foo)))) "["(number->string c0)"] " "= "  "{"
                   (let f ([e* e*]) 
                               (if (null? e*)
                                 ""
                                (string-append (c-aux (first e*) tabla) ","(f (rest e*)))) )"};")]
    [(,e0 ,e1) (string-append (c-aux e0 tabla)";\n"(c-aux e1 tabla)";")]
                                          ) )

