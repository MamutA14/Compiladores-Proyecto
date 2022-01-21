#lang nanopass
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

