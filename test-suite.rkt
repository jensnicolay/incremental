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

;extensions
(test-machine ''123 '123)

;warmup
;(test-machine (file->value "test/fib.scm")        21)
;(test-machine (file->value "test/collatz.scm")    5)

(test-machine (file->value "test/browse.scm")     '<undefined>)
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
                  
                                                        