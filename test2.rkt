#lang racket

; more extensive tests involving (more) primitives and checking results of benchmark programs

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

; support (prims etc)
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
(test-machine (file->value "test/fib.scm")        21)
(test-machine (file->value "test/collatz.scm")    5)

;(test-machine (file->value "test/browse.scm") '<undefined>)  ; correct, ±63 mins
(test-machine (file->value "test/churchnums.scm") #t)
(test-machine (file->value "test/classtree.scm") #f)
(test-machine (file->value "test/dderiv.scm") #t)
(test-machine (file->value "test/deriv.scm") #t)
(test-machine `(let ((result ,(file->value "test/destruc.scm"))) (tostring result)) "((() . ()) . ((1 . ()) . ((1 . (() . ())) . ((1 . (() . ())) . ((1 . (() . ())) . ((1 . (() . ())) . ((1 . (() . ())) . ((1 . (() . ())) . ((1 . (() . ())) . ((1 . (() . (() . (() . ())))) . ()))))))))))")
(test-machine (file->value "test/fannkuch.scm") 4)
;(test-machine (file->value "test/graphs.scm") 596) ; H-O cons
(test-machine (file->value "test/grid.scm") #t)
(test-machine `(let ((result ,(file->value "test/matrix.scm"))) (tostring result)) "(215 . (960 . (1220 . 1775)))")
;(test-machine (file->value "test/mazefun.scm") #t) ; TOO LONG
;(test-machine (file->value "test/mceval.scm") 2) ; TOO LONG
(test-machine (file->value "test/partialsums.scm") 77030060483083029083/96845140757687397075)
(test-machine (file->value "test/primtest.scm") 1)
(test-machine (file->value "test/regex.scm") #t)
(test-machine (file->value "test/scm2java.scm") "public class BOut extends RuntimeEnvironment {n public static void main (String[] args) {n((ProcValue1)(new NullProcValue1 () {n public Value apply(final Value x) {n final ValueCell m_x = new ValueCell(x);nn  return ((ProcValue1)(new NullProcValue1 () {n public Value apply(final Value f) {nn  return ((ProcValue1)(f)).apply(new IntValue(10))n ;n}}n)).apply(((ProcValue1)(((ProcValue1)(new NullProcValue1 () {n public Value apply(final Value h) {nn  return new NullProcValue1 () {n public Value apply(final Value F) {nn  return ((ProcValue1)(F)).apply(new NullProcValue1 () {n public Value apply(final Value x1) {nn  return ((ProcValue1)(((ProcValue1)(((ProcValue1)(h)).apply(h)n)).apply(F)n)).apply(x1)n ;n}}n)n ;n}}n ;n}}n)).apply(new NullProcValue1 () {n public Value apply(final Value h) {nn  return new NullProcValue1 () {n public Value apply(final Value F) {nn  return ((ProcValue1)(F)).apply(new NullProcValue1 () {n public Value apply(final Value x1) {nn  return ((ProcValue1)(((ProcValue1)(((ProcValue1)(h)).apply(h)n)).apply(F)n)).apply(x1)n ;n}}n)n ;n}}n ;n}}n)n)).apply(new NullProcValue1 () {n public Value apply(final Value f) {nn  return new NullProcValue1 () {n public Value apply(final Value n) {nn  return (n).toBoolean() ? (VoidValue.Void(m_x.value = new IntValue(3))) : (((ProcValue1)(new NullProcValue1 () {n public Value apply(final Value $_) {nn  return ((ProcValue1)(new NullProcValue1 () {n public Value apply(final Value $_) {nn  return f ;n}}n)).apply(n)n ;n}}n)).apply(m_x.value)n) ;n}}n ;n}}n)n)n ;n}}n)).apply(new IntValue(10))n ;n }n}n")
(test-machine (file->value "test/spectralnorm.scm") 1.1833501765516568)
(test-machine (file->value "test/supermerge.scm") #t)
(test-machine (file->value "test/treeadd.scm") 15)
;(test-machine `(let ((result ,(file->value "test/triangl.scm"))) (tostring result)) "(22 . (34 . (31 . (15 . (7 . (1 . (20 . (17 . (25 . (6 . (5 . (13 . (32 . ())))))))))))))") ; TOO LONG ;
;(test-machine (file->value "test/boyer.scm") #t) ; TOO LONG

(define end-time (current-milliseconds))

(printf "~v ms\n" (- end-time start-time))
                  
                                                        