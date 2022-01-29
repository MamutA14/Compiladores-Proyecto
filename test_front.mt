
;; para el pass 1
(remove-one-armed-if (parse-LF '(if 1 2)))

;; para el pass 2
(remove-string (remove-one-armed-if (parse-LF '(if cosa 2))))
(remove-string (remove-one-armed-if (parse-LF '(begin (if 1 2)))))


;; para el pass 4
(identify-assigments (curry-let (parse-L2 '(let ([x Lambda (lambda ([x Int]) x)] [y Int e2]) (primapp + x y e3) ))))


;; para parse 5
(un-anonymous (identify-assigments (curry-let (parse-L2 '(let ([x Lambda (lambda ([x Int]) x)] [y Int e2]) (primapp + x y (lambda ([z Int]) z )) )))))

;; para el pass 6
 (verify-arity (un-anonymous (identify-assigments (curry-let (parse-L2 '(if (primapp < 1 2) #t #f ))))))

;; para el pass 7
(verify-vars (verify-arity (un-anonymous (identify-assigments (curry-let (parse-L2 '(while (1) (primapp ++ 1) )))))))
(verify-vars (verify-arity (un-anonymous (identify-assigments (curry-let (parse-L2 '(for [x (1 2 3)] (primapp ++ x) )))))))

;; ejemplo con los passes completos
(front-passes (parse-LF '(for [x (1 2 3)] (primapp < 1 x))))
