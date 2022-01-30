;; para el pass 12
(assigment (middle-passes (front-passes (parse-LF '(begin (define x (quot 1)) (quot 2)) ))))
(assigment (middle-passes (front-passes (parse-LF '(let ([x Int  (quot 20)]) (primapp ++ x) )))))
(assigment (middle-passes (front-passes (parse-LF '(while ([(quot 1)]) (begin (define x (quot 3)) (quot 1) ) )      ))))
(assigment (middle-passes (front-passes (parse-LF '(for [x (list (quot 1))] (begin (define y (quot 1))) )      ))))
(list-to-array (assigment (middle-passes (front-passes (parse-LF '(for [x (list (quot 1))] (begin (define y (quot 1)) (define x (quot 2))) )      )))))


 (c (list-to-array (assigment (middle-passes (front-passes (parse-LF '(list (quot 1) (quot 2) )      ))))))
 (displayln (c (list-to-array (assigment (middle-passes (front-passes (parse-LF '(for [x (list (quot 13) (quot 15))] (primapp equal? x x) )      )))))))
 (displayln (c (list-to-array (assigment (middle-passes (front-passes (parse-LF '(begin (define x (quot 1)) (define y (quot 2)) (primapp < x y))      )))))))
