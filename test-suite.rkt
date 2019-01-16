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

;quote
(test-machine ''123 '123)
(test-machine ''() '())
(test-machine '(null? '()) #t)
(test-machine '(let ((x '(1))) (car x)) 1)
(test-machine '(let ((x '(1))) (cdr x)) '())
(test-machine '(let ((x '(1 2))) (car x)) 1)
(test-machine '(let ((x '(1 2))) (let ((p (cdr x))) (car p))) 2)
(test-machine '(let ((x '(1 2))) (let ((p (cdr x))) (cdr p))) '())
(test-machine '(let ((x '((1)))) (let ((p (car x))) (car p))) 1)
(test-machine '(let ((x '((1)))) (let ((p (car x))) (cdr p))) '())
(test-machine '(let ((x '((1 2)))) (let ((p (car x))) (let ((q (cdr p))) (car q)))) 2)
(test-machine '(let ((x '((1 2)))) (let ((p (car x))) (let ((q (cdr p))) (cdr q)))) '())
(test-machine '(let ((x '(1 (2)))) (let ((p (cdr x))) (let ((q (car p))) (car q)))) 2)
(test-machine '(let ((x '(1 (2)))) (let ((p (cdr x))) (let ((q (car p))) (cdr q)))) '())
(test-machine '(let ((x '(1 (2 3)))) (let ((p (cdr x))) (let ((q (car p))) (let ((r (cdr q))) (car r))))) 3)
(test-machine '(let ((x '(1 (2 3)))) (let ((p (cdr x))) (let ((q (car p))) (let ((r (cdr q))) (cdr r))))) '())
(test-machine '(let ((x '(1 (2 3)))) (let ((p (cdr x))) (let ((q (car p))) (car q)))) 2)

(test-machine '(let ((x 'a)) (let ((u (set! x 'b))) x)) 'b)
(test-machine '(let ((x '(a))) (let ((y '(b))) (let ((u (set! x y))) (car x)))) 'b)

(test-machine '(let ((x '(a))) (let ((u (set-car! x 'b))) (car x))) 'b)
(test-machine '(let ((x '(a))) (let ((u (set-cdr! x 'b))) (cdr x))) 'b)
(test-machine '(let ((x '(a))) (let ((u (set-cdr! x 'b))) (car x))) 'a)



;warmup
;(test-machine (file->value "test/fib.scm")        21)
;(test-machine (file->value "test/collatz.scm")    5)

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
                  
                                                        