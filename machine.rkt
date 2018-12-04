#lang racket

(require "general.rkt")
(require "ast.rkt")

(provide conc-eval)
(define ns (make-base-namespace))

;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)
(struct clo (e s) #:transparent)
 ; #:property prop:custom-write (lambda (v p w?)
  ;                               (fprintf p "<clo ~v>" (clo-e v))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))
(struct addr (a) #:transparent)
(struct binding (e κ) #:transparent)
(struct state (e κ) #:transparent)
(struct system (graph end-state parent) #:transparent)
(struct graph (fwd bwd initial) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(graph ~v :initial ~v)" (graph-fwd v) (graph-initial v))))


(define count!
  (let ((counter 0))
    (lambda ()
      (begin0
        counter
        (set! counter (add1 counter))))))

;;;

(define (successor s g)
  (hash-ref (graph-fwd g) s #f))

(define (predecessor s g)
  (hash-ref (graph-bwd g) s #f))

(define (body-expression? e parent)
  («lam»? (parent e)))


;(define (graph-eval e s g parent)
;  (graph-eval-path e '() s g parent))
  
(define (graph-eval e s g parent) ; general TODO: every fw movement should be restrained to previous path(s)
  (printf "ev ~v in ~v\n" e (user-print s))

  (let ((d-result
  (match e
    ((«lit» _ d)
     d)
    ((«id» _ x)
     (let ((d (lookup-path x '() s g parent)))
       d))
    ((«lam» _ e-params e-body)
     (clo e s))
    ((«let» _ _ _ e-body)
     (let ((s* (state e-body (state-κ s))))
       (graph-eval e-body s* g parent)))
    ((«if» _ _ _ _)
     (let ((s* (successor s g)))
       (graph-eval (state-e s*) s* g parent)))
    ((«set!» _ _ _)
     '<unspecified>)
    ((«app» _ («id» _ x) e-rands) ;TODO: ((lam ...) rands)
     (let ((κ (state-κ s)))
       (let ((s* (successor s g)))
         (match s*
           ((state (? (lambda (e) (body-expression? e parent)) e-body) _)
            ;(printf "\t~v: compound app with body ~v\n" e e-body)
            (graph-eval e-body s* g parent))
           (_
            (let ((d-rands (map (lambda (e-rand) (graph-eval e-rand s g parent)) e-rands))
                  (proc (eval (string->symbol x) ns)))
              ;(printf "~v: primitive app ~v on ~v\n" e x d-rands)
              (apply proc d-rands)))))))
    ((«car» _ (and e-id («id» _ x)))
     (let ((d (lookup-path x '(car) s g parent)))
       ;(printf "-> ~v\n" d)
       d))
    ((«cdr» _ (and e-id («id» _ x)))
     (let ((d (lookup-path x '(cdr) s g parent)))
       ;(printf "-> ~v\n" d)
       d))
    ((«cons» _ _ _)
      s)
    )))

    (printf "evalled ~v in ~v: ~v\n" e (user-print s) (user-print d-result))
    d-result
    ))


(define (lookup-path x field-path s g parent)
  (printf "lookup-path ~v ~v ~v\n" x field-path s)
  (let ((b-root (lookup-root x field-path s g parent)))
    (if b-root
        (if (null? field-path)
            (match-let (((cons e-b s*) b-root))
              (graph-eval e-b s* g parent))
            (lookup-path-dynamic b-root s g parent))
        (if (null? field-path)
            (eval (string->symbol x) ns)
            (error "!")))))


(define (lookup-root x field-path s g parent)
  (printf "lookup-root ~v ~v ~v\n" x field-path s)
  (let ((b (lookup-binding x s g parent)))
    (match-let (((binding e-b κ-b) b))

    (define (lookup-root-helper s s*)
        ;(printf "\tlookup-root-helper ~v\n" s*)
      (match s*
        (#f #f)
        ((state e κ)
         (match e
           ((«let» _ (== e-b) e-init _)
            (if (equal? κ κ-b)
                (follow-field-path e-init field-path s g parent)
                (lookup-root-helper s* (predecessor s* g))))
           ((«letrec» _ (== e-b) e-init _)
            (if (equal? κ κ-b)
                (follow-field-path e-init field-path s g parent)
                (lookup-root-helper s* (predecessor s* g))))
           ((«set!» _ («id» _ (== x)) e-update)
            (let ((b* (lookup-binding x s* g parent)))
              (if (equal? b b*)
                  (follow-field-path e-update field-path s* g parent)
                  (lookup-root-helper s* (predecessor s* g)))))
           ((«app» _ _ _)
            (if (and (body-expression? (state-e s) parent) ; s* is compound call, s is proc entry
                     (equal? (state-κ s) κ-b))
                (let* ((e-proc (parent (state-e s)))
                       (xs («lam»-x e-proc)))
                  (let param-loop ((xs xs) (e-args («app»-aes e)))
                    (if (null? xs)
                        (lookup-root-helper s* (predecessor s* g))
                        (if (equal? (car xs) e-b)
                            (follow-field-path (car e-args) field-path s* g parent)
                            (param-loop (cdr xs) (cdr e-args))))))
                (lookup-root-helper s* (predecessor s* g))))
           (_
            (lookup-root-helper s* (predecessor s* g)))
           ))
        ))

    (let ((b-root (lookup-root-helper s (predecessor s g))))
      (printf "looked up root expression for ~v: ~v\n" b b-root)
      b-root))))

(define (lookup-binding x s g parent)
  (printf "lookup-binding ~v ~v\n" x s)

  (define (ast-helper s)
    (let* ((e (state-e s))
           (κ (state-κ s))
           (pa (parent e)))
      ;(printf "\tast-helper ~v e ~v pa ~v\n" x e pa)
      (match pa
        ((«let» _ _ (== e) _)
         (ast-helper (state pa κ)))
        ((«let» _ (and e-decl («id» _ (== x))) _ _)
         (binding e-decl κ))
        ((«letrec» _ (and e-decl («id» _ (== x))) _ _)
         (binding e-decl κ))
        ;((«set!» _ _ (== e))
        ; (ast-helper (state pa κ)))
        ((«lam» _ (list xs ...) _) ; s evals body exp
         (let param-loop ((xs xs))
           (if (null? xs)
               (ast-helper (lookup-closure e κ))
               (let ((e-decl (car xs)))
                 (match e-decl
                   ((«id» _ (== x))
                    (binding e-decl κ))
                   (_
                    (param-loop (cdr xs))))))))
        (#f (binding #f #f))
        (_
         (ast-helper (state pa κ)))
        ))) ; no binding found

  (define (lookup-closure e κ)
    ;(printf "\tlookup-closure ~v ~v\n" e κ)
    (let ((s* (predecessor (state e κ) g)))
      (match s*
        ((state («app» _ e-rator _) _)
         (let ((d-clo (graph-eval e-rator s* g parent)))
           (printf "found lambda: ~v\n" d-clo)
           (clo-s d-clo))))
      ))

  (let ((res (ast-helper s)))
    (printf "looked up binding ~v: ~v\n" x res)
    res))


(define (follow-field-path e field-path s g parent)
  (printf "follow-path ~v ~v ~v\n" e field-path s)
  (if (null? field-path)
      (cons e s)
      (match e
        ((«id» _ x)
         (lookup-root x field-path s g parent))
        ((«let» _ _ _ e-body)
         (let ((s* (state e-body (state-κ s))))
           (follow-field-path e-body field-path s* g parent)))
        ((«if» _ _ _ _)
         (let ((s* (successor s g)))
           (follow-field-path (state-e s*) field-path s* g parent)))
        ((«app» _ e-rator e-rands)
         (let ((s* (successor s g)))
           (follow-field-path (state-e s*) field-path s* g parent)))
        ((«cons» _ e-car e-cdr)
         (match field-path
           ((cons 'car field-path*)
            (follow-field-path e-car field-path* s g parent))
           ((cons 'cdr field-path*)
            (follow-field-path e-cdr field-path* s g parent))
           ))
        ((«car» _ e-car) ; e-car can only be «id»...
         (follow-field-path e-car (cons 'car field-path) s g parent))
        ((«cdr» _ e-cdr)
         (follow-field-path e-cdr (cons 'cdr field-path) s g parent))
        )))


(define (lookup-path-dynamic b-root s g parent)
  (printf "lookup-dynamic ~v ~v\n" b-root s)
  (match-let (((cons e-b (state _ κ-b)) b-root))

    (define (lookup-dynamic-helper s)
        ;(printf "\tlookup-dynamic-helper ~v\n" s*)
        (match s
          (#f
           (error "unbound root" b-root))
          ((state e κ)
           (match e
             ((«cons» _ (== e-b) _)
              (if (equal? κ κ-b)
                  (graph-eval e-b s g parent)
                  (lookup-dynamic-helper (predecessor s g))))
             ((«cons» _  _ (== e-b))
              (if (equal? κ κ-b)
                  (graph-eval e-b s g parent)
                  (lookup-dynamic-helper (predecessor s g))))
;             ((«cons» _ (== e-b) (== e-b)) ; this cannot happen, e-b either needs to be car or cdr?
;              (error 'TODO))
             ((«set-car!» _ («id» _ x) e-update)
              (let ((b*-root (lookup-root x '(car) s g parent)))
                (let ((alias? (equal? b*-root b-root)))
                  ;(printf "binding ~v ~v root ~v alias of ~v ? ~v\n" b* '(car) b*-root b-root alias?)
                  (if alias?
                      (graph-eval e-update s g parent)
                      (lookup-dynamic-helper (predecessor s g))))))
             ((«set-cdr!» _ («id» _ x) e-update)
              (let ((b*-root (lookup-root x '(cdr) s g parent)))
                (let ((alias? (equal? b*-root b-root)))
                  ;(printf "binding ~v ~v root ~v alias of ~v ? ~v\n" b* '(cdr) b*-root b-root alias?)
                  (if alias?
                      (graph-eval e-update s g parent)
                      (lookup-dynamic-helper (predecessor s g))))))
             (_ ; TODO not all cases handled yet!
              (lookup-dynamic-helper (predecessor s g)))
             ))
          ))

    (let ((result (lookup-dynamic-helper (predecessor s g))))
      (printf "dynamically looked up ~v in ~v: ~v\n" b-root s result)
      result)))

(define (cont s g parent)
  ;(printf "cont e ~v κ ~v\n" e κ)

  (define (cont-helper e κ)
    (let ((p (parent e)))
      (match p
        ((«let» _ _ (== e) e-body)
         (state e-body κ))
        ((«letrec» _ _ (== e) e-body)
         (state e-body κ))
        ((«lam» _ _ (== e))
         (let ((s* (predecessor (state e κ) g)))
           ;(printf "pop e ~v κ ~v = ~v\n" e κ κs)
           (cont s* g parent)))
        (#f #f)
        (_ (cont-helper p κ))
        )))

  (cont-helper (state-e s) (state-κ s)))
  
  
  (define (step s g parent)
    (printf "\n#~v\nstep ~v\n" (state->statei s) s)
    (match-let (((state e κ) s))
      (match e
        ((«let» _ _ init _)
         (state init κ))
        ((«letrec» _ _ init _)
         (state init κ))
      ((«if» _ e-cond e-then e-else)
       (let ((d-cond (graph-eval e-cond s g parent)))
         (state (if d-cond e-then e-else) κ)))
      ((«app» _ e-rator e-rands)
       (let ((d-proc (graph-eval e-rator s g parent)))
         (match d-proc
           ((clo («lam» _ _ e-body) _)
            (let* ((κ* (count!))
                   (s* (state e-body κ*)))
              s*))
           ((? procedure?)
            (cont s g parent)))))
      (_ (cont s g parent))
      )))


(define (explore e)

  (define parent (make-parent e))
  
  (define g (graph (hash) (hash) #f))
  
  (define (add-transition! from to)
    (set! g (graph (hash-set (graph-fwd g) from to) (hash-set (graph-bwd g) to from) #f)))
  
  (define (explore! s)
    (let ((s* (step s g parent)))
      (if s*
          (begin
            ;(printf "TRANS ~v -> ~v\n" (state->statei s) (set-map succs state->statei))
            (add-transition! s s*)
            (explore! s*))
          s)))

  (let ((s0 (state e (count!))))
    (let ((s-end (explore! s0)))
      (system (graph (graph-fwd g) (graph-bwd g) s0) s-end parent)))) ;incremental-update)))

(define (evaluate e)
  (let* ((sys (explore e))
         (g (system-graph sys))
         (s-end (system-end-state sys))
         (parent (system-parent sys)))
    (printf "\n\nEXPLORED with end state ~v\n" (state->statei s-end))
    ;(generate-dot g "grapho")
    (graph-eval (state-e s-end) s-end g parent)))

(define (conc-eval e)
  (evaluate e))

;;; OUTPUT STUFF

(define (user-print d)
  (match d
    ((clo e s) `(clo ,e ,(user-print s)))
    ((state e κ) `(state ,(~a e #:max-width 20) ,κ))
    (_ d)))

(define (index v x)
  (let ((i (vector-member x v)))
    (if i
        i
        (let ((i (add1 (vector-ref v 0))))
          (vector-set! v 0 i)
          (vector-set! v i x)
          i))))
(define stateis (make-vector 2000))
(define (state->statei q) (index stateis q))

(define (state-repr s)
  (format "~v ~v" (state-e s) (state-κ s)))

(define (generate-dot g name)
  (let ((dotf (open-output-file (format "~a.dot" name) #:exists 'replace)))
  
    (define (dot-helper s)
      (let ((si (state->statei s)))
        (fprintf dotf "~a [label=\"~a | ~a\"];\n" si si (state-repr s))
        (let ((s* (successor s g)))
          (when s*
            (let ((si* (state->statei s*)))
              (fprintf dotf "~a -> ~a;\n" si si*)
              (dot-helper s*))))))
    
    (fprintf dotf "digraph G {\n")
    (let ((s0 (graph-initial g)))
      (dot-helper s0)
      (fprintf dotf "}")
      (close-output-port dotf))))

;;; TESTS

(module+ main
 (conc-eval
  (compile
   
   '(let ((f (lambda (x) x))) (let ((v (f 999))) v))
  
   )))
                      
                

               

;;; INTERESTING CASE is when the update exp of a set! can be non-atomic: first encountered set! when walking back is not the right one!
;;;; THEREFORE: we only allow aes as update exps
;;;(test '(let ((x 123)) (let ((y (set! x (set! x 456)))) x)) 'undefined)
;;;(test '(let ((x 123)) (let ((y (set! x (let ((u (set! x 456))) 789)))) x)) 789)

;;; SCHEME ERROR when setting before init
;;; (test '(letrec ((x (let ((u (set! x 123))) 456))) x) 456)