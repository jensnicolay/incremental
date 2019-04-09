#lang racket

(require "ast.rkt")
(require "machine.rkt")

(define (test-machine e expected)
  (let ((result
            (with-handlers ((exn:fail?
                             (lambda (exc) (if (eq? expected 'FAIL)
                                             'FAIL
                                             (begin
                                               (printf "unexpected failure for ~a:\n" e)
                                               (raise exc))))))
              (conc-eval (compile e)))))
         (unless (equal? result expected)
           (error (format "wrong result for ~a:\n\texpected ~a\n\tgot      ~a" e expected result)))))

(define start-time (current-milliseconds))

;support
(test-machine '(number->string 123) "123")
(test-machine '(= 0 0) #t)
(test-machine '(= 0 1) #f)
(test-machine '(let ((p '(1 2))) (cddr p)) '())
(test-machine '(let ((b (cons 1 2)))
                (let ((a (cons 0 b)))
                  (let ((xx (cddr a)))
                    (+ 1 xx)))) 3)
(test-machine '(let ((p (cons 1 2))) (eq? p p)) #t)
(test-machine '(let ((p (cons 1 2))) (let ((q (cons 1 2))) (eq? p q))) #f)
(test-machine '(let ((p (cons 1 2))) (let ((q p)) (eq? p q))) #t)
(test-machine '(let ((p (cons 1 2))) (pair? p)) #t)
(test-machine '(let ((p 123)) (pair? p)) #f)
(test-machine '(list) '())
(test-machine '(let ((l (list))) (eq? l '())) #t)
(test-machine '(let ((l (list))) (null? l)) #t)



(test-machine '(let ((p (cons 1 2))) (let ((q (cons 1 2))) (equal? p q))) #t)
(test-machine '(let ((p (cons 1 2))) (let ((q (cons 1 3))) (equal? p q))) #f)


;warmup
; (test-machine (file->value "test/fib.scm")        21)
; (test-machine (file->value "test/collatz.scm")    5)

;(test-machine (file->value "test/browse.scm")     '<undefined>)
;(test-machine (file->value "test/churchnums.scm") #t)
            ; "classtree"
            ; "dderiv"
            ; "deriv"
            ; "destruc"
            ; "fannkuch"
            ; "graphs"
            ; ;"grid"
            ; "matrix"
            ; "mazefun"
            ; "mceval"
            ; "partialsums"
            ; "primtest"
            ; "regex"
            ; "scm2java"
            ; "spectralnorm"
            ; "supermerge"
            ; "treeadd"
            ; "triangl"
            ; "boyer"

(define end-time (current-milliseconds))

(printf "~v ms\n" (- end-time start-time))
                  
                                                        