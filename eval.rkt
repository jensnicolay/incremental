#lang racket

(require "lattice.rkt")
(require "machine.rkt")
(require "semantics.rkt")

;; allocators
(define conc-alloc-counter 0)
(define conc-alloc
  (lambda _
    (set! conc-alloc-counter (add1 conc-alloc-counter))
    conc-alloc-counter))

(define (mono-alloc x _)
  x)

(define (poly-alloc x ctx)
  (cons x ctx))

(define conc-kalloc (lambda (e clo rands A) (ctx (conc-alloc) clo rands A)))
(define free-kalloc (lambda (e clo rands A) (ctx e clo rands A)))

;; semantics
(define conc-scheme-semantics (create-scheme-semantics conc-lattice conc-alloc conc-kalloc conc-alloc #t))
(define (conc-eval e)
  (let* ((sys (machine-eval e conc-scheme-semantics))
         (transitions (system-transitions sys))
         (⊔ (lattice-⊔ conc-lattice))
         (⊥ (lattice-⊥ conc-lattice))
         (answer-value (for/fold ((d ⊥)) ((s (in-list (hash-keys transitions))))
                         (⊔ d (answer-value s ⊥)))))
    answer-value))
