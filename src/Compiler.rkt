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

;; Ruta del archivode entrada de extension .mt
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
(define lf-code (parse-LF read-file))

;; Funcion que aplica las tres fases de compilacion a
;; un archivo de entrada con codigo en lenguaje fuente y escribe tres archivos
;; asociados a cada fase
;; TODO: Archivo middle, y back (codigo c este ultimo)


(define (compile-with-output lf-code path)  
  (write-file (pretty-format (front-end-passes lf-code)) (string-append path ".fe")))
  ;(write-file (pretty-format (processes-Middle-end exp)) (string-append path ".me")
  ;(write-file (pretty-format ((processes-Back-end exp)) (string-append path ".c"))

;; Definicion de los pases en cada una de las 3 fases de compilación

(define (front-end-passes lf-code)
  (verify-vars
   (verify-arity
    (un-anonymous
     (identify-assignments
      (curry-let
       (remove-string
         (remove-one-armed-if lf-code))))))))

(println "Codigo de LF en el archivo de entrada:")
lf-code
(println "Codigo intermedio tras la fase de front-end:")
(front-end-passes lf-code)
