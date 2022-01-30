;;para el pass 12
(assigment (parse-L7 '(letrec ([foo (Int -> Int) (lambda ([x Int]) x)]) (foo (const Int 5)))))
(assigment (parse-L7 '(let ([x Int (primapp * (const Int 40) (const Int 20))]) (primapp cdr x))))


;;para el pass 13 
(list-to-array ’( list 1 2 3 4 5) )
(list-to-array ’( list #\a #\b #\c 'd))
;;Para c 
(c (parse-L9 '(if (const Bool #t) (primapp + (const Int 2) (const Int 2)) (primapp - (const Int 2) (const Int 2)))))
(c (parse-L9  '(let x  (primapp + x (const Int 4)) )))    
