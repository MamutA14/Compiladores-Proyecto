;; para el pass 8
(curry (front-passes (parse-LF '(lambda ([x Int] [y Int]) x ))))

;; para el pass 9
(type-const (curry (front-passes (parse-LF '((lambda ([x Int] [y Int]) x ) (quot 1) ) ))))
