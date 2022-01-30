#|
Compiladores 2022-1  Proyecto Final 
Alumnos:
- Acosta Meza Alam
  No.cuenta : 315124569
- Arroyo Rivera Juan José
  No.cuenta: 416053223
- Sierra Casiano Vladimir
  No.cuenta: 316020361
|#

#lang nanopass
(require racket/pretty)

(require "frontend.rkt")
(require "middle.rkt")
(require "backend.rkt")

;; Ruta del archivo de entrada de extension .mt
(define path "ejemplo1")

;; Funcion para abrir el archivo
(define (read-file path)
  (read (open-input-file (string-append path ".mt"))))

;; Funcion que escribe en un archivo el codigo obtenido al aplicar los passes en la
;; compilacion 
(define (write-file code path)
  (with-output-to-file path
   (lambda () (printf "~a" code))
   #:mode 'text #:exists 'replace))

;; Codigo parseado del archivo inicial de entrada
(define lf-code (parse-LF (read-file path)))




;; Definicion de los pases en cada una de las 3 fases de compilación

;; Passes del front-end 
(define (front-end-passes lf-code)
  (verify-vars
   (verify-arity
    (un-anonymous
     (identify-assigments
      (curry-let
       (remove-string
         (remove-one-armed-if lf-code))))))))

;; Passes del middle-end
(define (middle-end-passes exp)
  (uncurry
   (type-infer
    (type-const
     (curry
      (front-end-passes exp))))))

;; Passes del back-end
(define (back-end-passes exp)
  (c
   (list-to-array
    (assigment
     (middle-end-passes exp)))))


;; Se aplican las tres fases de compilacion a
;; un archivo de entrada con codigo en lenguaje fuente y escribe tres archivos
;; asociados a cada fase
(write-file (pretty-format (front-end-passes lf-code))(string-append path ".fe"))
(write-file (pretty-format (middle-end-passes lf-code)) (string-append path ".me"))
(write-file (pretty-format (back-end-passes lf-code)) (string-append path ".c"))

(println "Codigo de LF en el archivo de entrada:")
lf-code
(println "Codigo intermedio tras la fase de front-end (ejemplo.fe):")
(front-end-passes lf-code)
(println "Codigo intermedio tras la fase de middle-end (ejemplo.me):")
(middle-end-passes lf-code)
(println "Codigo intermedio tras la fase de middle-end (ejemplo.c):")
(back-end-passes lf-code)
