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

(test-machine '123 123)
(test-machine '(let ((x 10)) x) 10)
(test-machine '(let ((x 10)) (let ((y 20)) y)) 20)
(test-machine '(let ((x 10)) (let ((y 20)) x)) 10)
(test-machine '(let ((x 10)) (let ((x 20)) x)) 20)
(test-machine '(let ((x 123)) (let ((u (let ((x #f)) "dummy"))) x)) 123)

(test-machine '(+ 1 1) 2)
(test-machine '(let ((x (+ 1 1))) x) 2)
(test-machine '(let ((x (let ((z 3)) z))) x) 3)
(test-machine '(let ((f (lambda () (- 5 3)))) (f)) 2)
(test-machine '(let ((f (lambda (x) (* x x)))) (f 4)) 16)
(test-machine '(let ((f (lambda (x) x))) (let ((v (+ 3 9))) v)) 12)
(test-machine '(let ((x 123)) (let ((f (lambda () x))) (f))) 123)
(test-machine '(let ((f (lambda (x) x))) (let ((v (f 999))) v)) 999)
(test-machine '(let ((g (lambda (v) v))) (let ((f (lambda (n) (let ((m (g 123))) (* m n))))) (f 2))) 246)
(test-machine '(let ((f (lambda (x) x))) (let ((u (f 1))) (f 2))) 2)
(test-machine '(let ((f (lambda (y) (let ((x y)) x)))) (let ((z (f "foo"))) (f 1))) 1)
(test-machine '(let ((f (lambda (x) (let ((v x)) v)))) (f 123)) 123)
(test-machine '(let ((f (lambda (x) (let ((i (lambda (a) a))) (i x))))) (let ((z1 (f 123))) (let ((z2 (f #t))) z2))) #t)

(test-machine '(if #t 1 2) 1)
(test-machine '(if #f 1 2) 2)
(test-machine '(if #t (+ 3 5) (- 4 6)) 8)
(test-machine '(if #f (+ 3 5) (- 4 6)) -2)
(test-machine '(let ((f (lambda (x) (* x x)))) (let ((v (f 4))) (if v (f 5) (f 6)))) 25)
(test-machine '(if #t (let ((x 1)) x) (let ((x 2)) x)) 1)
(test-machine '(if #f (let ((x 1)) x) (let ((x 2)) x)) 2)
(test-machine '(let ((x (if #t 1 2))) x) 1)
(test-machine '(let ((x (if #f 1 2))) x) 2)

(test-machine '(let ((f (lambda (x) (lambda (y) x)))) (let ((v (f 123))) (v 999))) 123)
(test-machine '(let ((f (lambda (x) (lambda (x) x)))) (let ((v (f 123))) (v 999))) 999)
(test-machine '(let ((f (lambda (g) (g 678)))) (let ((id (lambda (x) x))) (f id))) 678)
(test-machine '(let ((f (lambda (g x) (g x)))) (let ((id (lambda (x) x))) (f id 789))) 789)
(test-machine '(let ((f (lambda (g) (lambda (x) (g x))))) (let ((sq (lambda (x) (* x x)))) (let ((ff (f sq))) (ff 11)))) 121)


(test-machine '(letrec ((f (lambda (x) (if x "done" (f #t))))) (f #f)) "done")
(test-machine '(letrec ((f (lambda (x) (let ((v (= x 2))) (if v x (f (+ x 1))))))) (f 0)) 2)
(test-machine '(letrec ((fac (lambda (n) (let ((v (= n 0))) (if v 1 (let ((m (- n 1))) (let ((w (fac m))) (* n w)))))))) (fac 1)) 1)
(test-machine '(letrec ((fac (lambda (n) (let ((v (= n 0))) (if v 1 (let ((m (- n 1))) (let ((w (fac m))) (* n w)))))))) (fac 3)) 6)
(test-machine '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((n2 (- n 2))) (let ((f1 (fib n1))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 1)) 1)
(test-machine '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((f1 (fib n1))) (let ((n2 (- n 2))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 1)) 1)
(test-machine '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((n2 (- n 2))) (let ((f1 (fib n1))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 3)) 2)
(test-machine '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((f1 (fib n1))) (let ((n2 (- n 2))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 3)) 2)
(test-machine '(letrec ((count (lambda (n) (let ((t (= n 0))) (if t 123 (let ((u (- n 1))) (let ((v (count u))) v))))))) (count 8)) 123)

(test-machine 'x 'FAIL)
(test-machine '(let ((f (lambda () f))) (f)) 'FAIL)

; set!
(test-machine '(let ((x 123)) (let ((u (if #t (set! x 456) (set! x 789)))) x)) 456)
(test-machine '(let ((x 123)) (let ((u (if #f (set! x 456) (set! x 789)))) x)) 789)
(test-machine '(let ((y 999)) (let ((x 123)) (let ((u (if x (set! y 456) (set! y 789)))) y))) 456)
(test-machine '(let ((x 123)) (let ((u (set! x 456))) x)) 456)
(test-machine '(let ((x 123)) (let ((u (set! x 456))) (let ((uu (set! x 789))) x))) 789)
(test-machine '(let ((x 123)) (let ((u (if x (set! x 456) (set! x 789)))) x)) 456)
(test-machine '(let ((x 123)) (let ((u (set! x #f))) (let ((uu (if x (set! x 456) (set! x 789)))) x))) 789)
(test-machine '(let ((x #t)) (let ((f (lambda () (set! x #f)))) (let ((u (f))) x))) #f)
(test-machine '(let ((x #t)) (let ((g (lambda () (set! x #f)))) (let ((f (lambda (h) (h)))) (let ((u (f g))) x)))) #f)
(test-machine '(let ((x 2)) (let ((f (lambda (y) (let ((oldx x)) (let ((_ (set! x y))) oldx))))) (f 1))) 2)
(test-machine '(let ((x 1)) (let ((f (lambda (y) (let ((oldx x)) (let ((_ (set! x y))) oldx))))) (let ((__ (f "foo"))) (f 1)))) "foo")
(test-machine '(let ((x 1)) (let ((f (lambda (y) (let ((oldx x)) (let ((_ (set! x y))) oldx))))) (let ((_ (f 1))) (let ((__ (f "foo"))) (f 1))))) "foo")
(test-machine '(let ((f (lambda (x) (let ((y (set! x "hoho"))) x)))) (f 1)) "hoho")
(test-machine '(let ((f (lambda (x) (let ((y (set! x "hehe"))) x)))) (let ((u (f 1))) (f 2))) "hehe")
(test-machine '(let ((x 123)) (let ((f (lambda (y) y))) (let ((v (set! x 456))) (let ((u (f v))) x)))) 456)
(test-machine '(let ((x 123)) (let ((f (lambda (x) x))) (let ((v (set! x 456))) (let ((u (f v))) x)))) 456)
(test-machine '(let ((x 123)) (let ((f (lambda (x y) x))) (let ((v (set! x 456))) (let ((u (f v 789))) x)))) 456)
(test-machine '(let ((x 123)) (let ((c (set! x 456))) (let ((u (if c 789 0))) x))) 456)
(test-machine '(let ((x 123)) (let ((c (set! x 456))) (let ((u (if c (set! x 789) (set! x 0)))) x))) 789)
(test-machine '(let ((x 123)) (let ((y (set! x 456))) x)) 456)
(test-machine '(let ((x 123)) (let ((y (set! x 456))) (let ((u (set! x 789))) x))) 789)
(test-machine '(let ((x 123)) (let ((y (set! x 456))) (let ((u (let ((z (set! x 789))) 0))) x))) 789)
(test-machine '(let ((x 123)) (let ((y (set! x 456))) (let ((u (set! x 0))) (let ((uu (let ((z (set! x 789))) 0))) x)))) 789)



                  
                  
                  
                                                        