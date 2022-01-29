#lang nanopass

(require "frontend.rkt")
(require "middle.rkt")
(provide (all-defined-out))

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
