;; para el pass 8
(curry (front-passes (parse-LF '(lambda ([x Int] [y Int]) x ))))

;; para el pass 9
(type-const (curry (front-passes (parse-LF '((lambda ([x Int] [y Int]) x ) (quot 1) ) ))))
(type-const (curry (front-passes (parse-LF '(letrec ([f Lambda (lambda ([x Int])x )]) (f (quot 1)) ) ))))


;; para el algoritmo J
(J (type-const (curry (front-passes (parse-LF '(primapp cons (quot 1) (list (quot 1)) ) )))) '())
(J (type-const (curry (front-passes (parse-LF '(for [x (list (quot 1)) ] x) )))) '())
(J (type-const (curry (front-passes (parse-LF '(while [(quot 1)] (primapp + (quot 1) (quot 2) )) )))) '())



;; para el pass 10
(type-infer (type-const (curry (front-passes (parse-LF '(letrec ([f Lambda (lambda ([x Int])x )]) (f (quot 1)) ) )))))
(type-infer (type-const (curry (front-passes (parse-LF '(let ([x List (list)]) x)) ))))
(type-infer (type-const (curry (front-passes (parse-LF '(let ([x List (list (quot 1) (quot 2))]) x)) ))))


