#lang racket

(require "general.rkt")
(require "ast.rkt")

(define (generate-agda e)
    (match e
        ((«lit» l d) (format "(«lit» ~a ~a)" l d))
        ((«id» l x) (format "(«id» ~a ~v)" l x))
        ((«lam» l (cons e0 '()) e1) (format "(«lam» ~a ~a ~a)" l (generate-agda e0) (generate-agda e1)))
        ((«let» l e0 e1 e2) (format "(«let» ~a ~a ~a ~a)" l (generate-agda e0) (generate-agda e1) (generate-agda e2)))
        ((«app» l e0 (cons e1 '())) (format "(«app» ~a ~a ~a)" l (generate-agda e0) (generate-agda e1)))
        ((«set!» l e0 e1) (format "(«set!» ~a ~a ~a)" l (generate-agda e0) (generate-agda e1)))
        ((«cons» l e-car e-cdr) (format "(«cons» ~a ~a ~a)" l (generate-agda e-car) (generate-agda e-cdr)))
        ((«car» l x) (format "(«car» ~a ~a)" l (generate-agda x)))
        ((«cdr» l x) (format "(«cdr» ~a ~a)" l (generate-agda x)))
        ((«set-car!» l x e) (format "(«set-car!» ~a ~a ~a)" l (generate-agda x) (generate-agda e)))
        ((«set-cdr!» l x e) (format "(«set-cdr!» ~a ~a ~a)" l (generate-agda x) (generate-agda e)))
    ))



(module+ main
(printf "~a\n"
 (generate-agda
  (compile

       '(let ((x (cons 0 1)))
                (let ((y x))
                  (let ((u (set-cdr! y 9)))
                    (cdr x))))

  ))))
