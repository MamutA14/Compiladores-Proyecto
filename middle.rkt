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


