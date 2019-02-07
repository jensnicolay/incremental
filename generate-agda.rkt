#lang racket

(require "general.rkt")
(require "ast.rkt")

(define (generate-agda e)
    (match e
        ((«lit» l d) (format "(«lit» ~a ~a)" l d))
        ((«id» l x) (format "(«id» ~a ~v)" l x))
        ((«lam» l (cons e0 '()) e1) (format "(«lam» ~a ~a ~a)" l (generate-agda e0) (generate-agda e1)))
        ((«let» l e0 e1 e2) (format "(«let» ~a ~a ~a ~a)" l (generate-agda e0) (generate-agda e1) (generate-agda e2)))
        ((«app» l e0 (cons e1 '())) (format "(«app» ~a ~a ~a)" l (generate-agda e0) (generate-agda e1)))))



(module+ main
(printf "~a\n"
 (generate-agda
  (compile

       '(let ((x 4))
          (let ((y 5))
            x))

  ))))
