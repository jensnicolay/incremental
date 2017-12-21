#lang racket

(require "semantics.rkt")

(provide (struct-out system))
(provide answer-value)
(provide machine-eval)

;;;;;;;;;;

(random-seed 111) ; deterministic random
(define CESK-TIMELIMIT (make-parameter 2)) ; timeout in minutes

;; machine
(struct ev (e ρ σ ι κ Ξ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "EV ~a\nρ ~a\nι ~a\nκ ~a" (ev-e v) (ev-ρ v) (ev-ι v) (ev-κ v))))
(struct ko (d σ ι κ Ξ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "KO v ~a\nι ~a\nκ ~a" (ko-d v) (ko-ι v) (ko-κ v))))
(struct system (status transitions duration initial) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<sys #~a ~a>" (~a (system-status v) #:max-width 70) (hash-count (system-transitions v)))))

(struct machine (inject step))

(define (create-machine semantics)

  (define (inject0 e)
    ((semantics-inject semantics) e ev))

  (define (step0 s)
    (define succ (set))
    (define (evaluate e ρ σ ι κ Ξ)
      (set! succ (set-add succ (ev e ρ σ ι κ Ξ))))
    (define (continue d σ ι κ Ξ)
      (set! succ (set-add succ (ko d σ ι κ Ξ))))
    (match s
      ((ev e ρ σ ι κ Ξ) ((semantics-evaluate semantics) e ρ σ ι κ Ξ evaluate continue))
      ((ko d σ ι κ Ξ) ((semantics-continue semantics) d σ ι κ Ξ evaluate continue)))
    succ)

  (machine inject0 step0))

(define (answer-value s ⊥)
  (match s
    ((ko d _ '() #f _) d)
    (_ ⊥)))
        
(define (explore initial step)
  
  (define time-limit (+ (current-milliseconds) (* (CESK-TIMELIMIT) 60000)))
  
  (define (explore-loop W T)
    (if (and (zero? (remainder (hash-count T) 10000))
             (> (current-milliseconds) time-limit))
        (system 'time-out T (- (current-milliseconds) start) initial)
        (if (set-empty? W)
            (system 'ok T (- (current-milliseconds) start) initial)
            (let* ((s (set-first W)))
              (if (hash-has-key? T s)
                  (explore-loop (set-rest W) T)
                  (let* ((succ (step s))
                         (W* (set-union W succ))
                         (T* (hash-set T s (set-union (hash-ref T s (set)) succ))))
                    (explore-loop W* T*)))))))
  
  (define start (current-milliseconds))
  (explore-loop (set initial) (hash)))
    
(define (machine-eval e semantics)
  (let* ((machine (create-machine semantics))
         (initial ((machine-inject machine) e))
         (sys (explore initial (machine-step machine))))
    sys))
