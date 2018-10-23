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
(struct binding (x e κ) #:transparent)
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

(define (state-exists? s g)
  (hash-ref (graph-fwd g) s #f))

(define (body-expression? e parent)
  («lam»? (parent e)))


(define (ev e s g parent)

  (define (eval-path e field-path s) ; general TODO: every fw movement should be restrained to previous path(s)
    (printf "ev ~v ~v in ~v\n" e field-path s)
    (match e
    ((«lit» _ d) ;(printf "-> ~v\n" ((lattice-α lat) d))
     d)
      ((«id» _ x)
       (let ((d (lookup-variable x s g parent))) ;(printf "-> ~v\n" d)
         d))
      ((«lam» _ e-params e-body) ;(printf "-> clo ~v\n" s)
       (clo e s))
      ((«let» _ _ _ e-body)
       (let graph-fw ((s* (successor s g)))
         (match s*
           ((state (== e-body) (== (state-κ s)))
            (eval-path e-body '() s*))
           (_
            (graph-fw (successor s* g))))))
      ((«if» _ _ _ _)
       (let ((s* (successor s g)))
         (eval-path (state-e s*) '() s*)))
      ((«set!» _ _ _)
       '<undefined>)
      ((«app» _ («id» _ x) e-rands) ;TODO: ((lam ...) rands)
       (let ((κ (state-κ s)))
         (let ((s* (successor s g)))
           (match s*
             (#f
              (let ((d-rands (map (lambda (e-rand) (eval-path e-rand '() s)) e-rands))
                    (proc (eval (string->symbol x) ns)))
                ;(printf "~v: primitive app ~v on ~v\n" e x d-rands)
                (apply proc d-rands)))
             ((state (? (lambda (e) (body-expression? e parent)) e-body) _)
              ;(printf "\t~v: compound app with body ~v\n" e e-body)
              (eval-path e-body '() s*))
             (_
              (let ((d-rands (map (lambda (e-rand) (eval-path e-rand '() s)) e-rands))
                    (proc (eval (string->symbol x) ns)))
                ;(printf "~v: primitive app ~v on ~v\n" e x d-rands)
                (apply proc d-rands)))))))
      ((«car» _ (and e-id («id» _ x)))
       (let ((d (lookup-path x (cons 'car field-path) s g parent)))
         ;(printf "-> ~v\n" d)
         d))
      ((«cdr» _ (and e-id («id» _ x)))
       (let ((d (lookup-path x (cons 'cdr field-path) s g parent)))
         ;(printf "-> ~v\n" d)
         d))
      ((«cons» _ ar dr)
       (match field-path
         ('() s)
         ((cons 'car field-path*) (eval-path ar field-path* s))
         ((cons 'cdr field-path*) (eval-path dr field-path* s))))
      ))
  
  (eval-path e '() s))


(define (graph-find-bw g s e κ)
  (let graph-fw ((s* (predecessor s g)))
    (match s*
      (#f #f)
      ((state (== e) (== κ))
       s*)
      (_
       (graph-fw (predecessor s* g))))))

(define (lookup-variable x s g parent)
  (printf "lookup-variable ~v ~v\n" x s)
  (let ((b (lookup-static x s g parent)))
    (lookup-var-dynamic b s g parent)))

(define (lookup-static x s g parent)
  (printf "lookup-static ~v ~v\n" x s)

  (define (ast-helper s)
    (let* ((e (state-e s))
           (κ (state-κ s))
           (pa (parent e)))
      ;(printf "ast-helper ~v e ~v pa ~v\n" x e pa)
      (match pa
        ((«let» _ _ (== e) _)
         (ast-helper (graph-find-bw g s pa κ)))
        ((«let» _ (and e-decl («id» _ (== x))) _ _)
         (binding x e-decl κ))
        ((«letrec» _ (and e-decl («id» _ (== x))) _ _)
         (binding x e-decl κ))
        ((«letrec» _ _ _ _)
         (ast-helper (graph-find-bw g s pa κ)))
        ((«set!» _ _ (== e))
         (ast-helper (graph-find-bw g s pa κ)))
        ((«lam» _ (list xs ...) _) ; s evals body exp
         (let param-loop ((xs xs))
           (if (null? xs)
               (ast-helper (find-lambda s pa))
               (let ((e-decl (car xs)))
                 (match e-decl
                   ((«id» _ (== x))
                    (binding x e-decl κ))
                   (_
                    (param-loop (cdr xs))))))))
        (#f (binding x #f #f))
        (_
         (ast-helper (graph-find-bw g s pa κ)))
        ))) ; no static decl found

  (define (find-lambda s pa) ; s should eval body expr
    ;(printf "find-lambda ~v ~v\n" s pa)
    (let ((s* (predecessor s g)))
      (match s*
        ((state («app» _ e-rator _) _)
         (let ((clo (ev e-rator s* g parent)))
           (clo-s clo))))
      ))

  (let ((res (ast-helper s)))
    (printf "looked up static ~v = ~v\n" x res)
    res))

(define (lookup-var-dynamic b s g parent)
  (printf "lookup-dynamic ~v ~v\n" b s)
  (match-let (((binding x e-b κ-b) b))

    (define (lookup-dynamic-helper s)
      (let ((s* (predecessor s g)))
        (match s*
          (#f
           (eval (string->symbol x) ns))
          ((state e κ)
           (match e
             ((«let» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (ev e-init s g parent)
                  (lookup-dynamic-helper s*)))
             ((«letrec» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (ev e-init s g parent)
                  (lookup-dynamic-helper s*)))
             ((«set!» _ («id» _ (== x)) e-update)
              (let ((b* (lookup-static x s* g parent)))
                (if (equal? b b*)
                    (ev e-update s* g parent)
                    (lookup-dynamic-helper s*))))
             ((«app» _ _ _)
              (if (and (body-expression? (state-e s) parent) ; s* is compound call, s is proc entry
                       (equal? (state-κ s) κ-b))
                  (let* ((e-proc (parent (state-e s)))
                         (xs («lam»-x e-proc)))
                    (let param-loop ((xs xs) (e-args («app»-aes e)))
                      (if (null? xs)
                          (lookup-dynamic-helper s*)
                          (if (equal? (car xs) e-b)
                              (ev (car e-args) s* g parent)
                              (param-loop (cdr xs) (cdr e-args))))))
                  (lookup-dynamic-helper s*)))
             (_
              (lookup-dynamic-helper s*))
             ))
          )))

    (lookup-dynamic-helper s)))


(define (lookup-path x field-path s g parent)
  (printf "lookup-path ~v ~v ~v\n" x field-path s)
  (let ((b (lookup-static x s g parent)))
    (let ((b-root (lookup-root-expression b field-path s g parent)))
      ;(printf "root of ~v ~v is ~v\n" b field-path b-root)
      (lookup-path-dynamic b-root s g parent))))


(define (follow-field-path e field-path s g parent)
  (printf "follow-path ~v ~v ~v\n" e field-path s)
  (match e
    ((«cons» _ e-car e-cdr)
     (match field-path
       ((cons 'car field-path*)
        (if («id»? e-car)
            (let ((b (lookup-static («id»-x e-car) s g parent)))
              (lookup-root-expression b field-path* s g parent))
            (cons e-car (state-κ s))))
       ((cons 'cdr field-path*)
        (if («id»? e-cdr)
            (let ((b (lookup-static («id»-x e-cdr) s g parent)))
              (lookup-root-expression b field-path* s g parent))
            (cons e-cdr (state-κ s))))
       ))
    ((«car» _ («id» _ x-car))
     (let ((b (lookup-static x-car s g parent)))
       (lookup-root-expression b (cons 'car field-path) s g parent)))
    ((«cdr» _ («id» _ x-cdr))
     (let ((b (lookup-static x-cdr s g parent)))
       (lookup-root-expression b (cons 'cdr field-path) s g parent)))
    ((«id» _ x)
     (let ((b (lookup-static x s g parent)))
       (lookup-root-expression b field-path s g parent)))
    ((«app» _ e-rator e-rands)
     (let ((s* (successor (successor s g) g)))
       (follow-field-path (state-e s*) field-path s* g parent)))
    ))

(define (lookup-root-expression b field-path s g parent)
  (printf "lookup-root-expression ~v ~v\n" b s)
  (match-let (((binding x e-b κ-b) b))

    (define (lookup-root-expression-helper s)
      (let ((s* (predecessor s g)))
        (match s*
          (#f (error "no root expression found"))
          ((state e κ)
           (match e
             ((«let» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (follow-field-path e-init field-path s* g parent)
                  (lookup-root-expression-helper s*)))
             ((«set!» _ («id» _ x) e-update)
              (let ((b* (lookup-static x s* g parent)))
                (if (equal? b b*)
                    (follow-field-path e-update field-path s* g parent)
                    (lookup-root-expression-helper s*))))
             ((«app» _ _ _)
              (if (and (body-expression? (state-e s) parent) ; s* is compound call, s is proc entry
                       (equal? (state-κ s) κ-b))
                  (let* ((e-proc (parent (state-e s)))
                         (xs («lam»-x e-proc)))
                    (let param-loop ((xs xs) (e-args («app»-aes e)))
                      (if (null? xs)
                          (lookup-root-expression-helper s*)
                          (if (equal? (car xs) e-b)
                              (follow-field-path (car e-args) field-path s* g parent)
                              (param-loop (cdr xs) (cdr e-args))))))
                  (lookup-root-expression-helper s*)))
             (_
              (lookup-root-expression-helper s*))
             ))
          )))

    (lookup-root-expression-helper s)))

(define (lookup-path-dynamic b-root s g parent)
  (printf "lookup-dynamic2 ~v ~v\n" b-root s)
  (match-let (((cons e-b κ-b) b-root))

    (define (lookup-dynamic2-helper s)
      (let ((s* (predecessor s g)))
        (match s*
          (#f
           (error "unbound root" b-root))
          ((state e κ)
           (match e
             ((«set-car!» _ («id» _ x) e-update)
              (let ((b* (lookup-static x s g parent)))
                (let ((b*-root (lookup-root-expression b* '(car) s* g parent)))
                  (let ((alias? (equal? b*-root b-root)))
                    ;(printf "binding ~v ~v root ~v alias of ~v ? ~v\n" b* '(car) b*-root b-root alias?)
                    (if alias?
                        (ev e-update s* g parent)
                        (lookup-dynamic2-helper s*))))))
             ((«set-cdr!» _ («id» _ x) e-update)
              (let ((b* (lookup-static x s g parent)))
                (let ((b*-root (lookup-root-expression b* '(cdr) s* g parent)))
                  (let ((alias? (equal? b*-root b-root)))
                    ;(printf "binding ~v ~v root ~v alias of ~v ? ~v\n" b* '(cdr) b*-root b-root alias?)
                    (if alias?
                        (ev e-update s* g parent)
                        (lookup-dynamic2-helper s*))))))
             ((«cons» _  (== e-b) (== e-b))
              'TODO)
             ((«cons» _  (== e-b) _)
              (if (equal? κ κ-b)
                  (ev e-b s* g parent)
                  (lookup-dynamic2-helper s*)))
             ((«cons» _  _ (== e-b))
              (if (equal? κ κ-b)
                  (ev e-b s* g parent)
                  (lookup-dynamic2-helper s*)))
             (_ ; TIODO not all cases handled yet!
              (lookup-dynamic2-helper s*))
             ))
          )))

    (lookup-dynamic2-helper s)))

(define (explore e)

  (define parent (make-parent e))
  
  ; state -> (set state...)
  (define fwd (hash))
  (define bwd (hash))
  
  (define (add-transition! from to)
    (set! fwd (hash-set fwd from to))
    (set! bwd (hash-set bwd to from)))
     
  (define (stack-pop s κ)
    (match s
      ((state (? (lambda (e) (body-expression? e parent))) (== κ))
       (hash-ref bwd s))
      (_
       (let ((s* (hash-ref bwd s)))
         (stack-pop s* κ)))))
               
      
  (define (cont e κ)
    ;(printf "cont e ~v κ ~v\n" e κ)
    (let ((p (parent e)))
      (match p
        ((«let» _ _ (== e) e-body)
         (state e-body κ))
        ((«letrec» _ _ (== e) e-body)
         (state e-body κ))
        ((«lam» _ _ (== e))
         (let ((s* (stack-pop (state e κ) κ)))
           ;(printf "pop e ~v κ ~v = ~v\n" e κ κs)
           (cont (state-e s*) (state-κ s*))))
        (#f #f)
        (_ (cont p κ))
        )))
  
  (define (step s)
    (printf "\n#~v\nstep ~v\n" (state->statei s) s)
    (match-let (((state e κ) s))
      (match e
        ((«let» _ _ init _)
         (state init κ))
        ((«letrec» _ _ init _)
         (state init κ))
        ((«if» _ e-cond e-then e-else)
         (let* ((g (graph fwd bwd #f))
                (d-cond (ev e-cond s g parent)))
           (state (if d-cond e-then e-else) κ)))
        ((«app» _ e-rator e-rands)
         (let* ((g (graph fwd bwd #f))
                (d-proc (ev e-rator s g parent)))
           (match d-proc
             ((clo («lam» _ _ e-body) _)
              (let* ((κ* (count!))
                     (s* (state e-body κ*)))
                s*))
             ((? procedure?)
              (cont e κ)))))
        (_ (cont e κ))
        )))

  (define (explore! s)
    (let ((s* (step s)))
      (if s*
          (begin
            ;(printf "TRANS ~v -> ~v\n" (state->statei s) (set-map succs state->statei))
            (add-transition! s s*)
            (explore! s*))
          s)))

  (let ((s0 (state e (count!))))
    (let ((s-end (explore! s0)))
      (system (graph fwd bwd s0) s-end parent)))) ;incremental-update)))

(define (evaluate e)
  (let* ((sys (explore e))
         (g (system-graph sys))
         (s-end (system-end-state sys))
         (parent (system-parent sys)))
    (printf "\n\nEXPLORED with end state ~v\n" (state->statei s-end))
    ;(generate-dot g "grapho")
    (ev (state-e s-end) s-end g parent)))

(define (conc-eval e)
  (evaluate e))

;;; OUTPUT STUFF

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
  (compile '(let ((x 1))
             (let ((y (+ x 1)))
               (let ((c (= y 2)))
                 (let ((z (if c (set! x 2) (set! x 3))))
                   (+ x y))))))))

;;; INTERESTING CASE is when the update exp of a set! can be non-atomic: first encountered set! when walking back is not the right one!
;;;; THEREFORE: we only allow aes as update exps
;;;(test '(let ((x 123)) (let ((y (set! x (set! x 456)))) x)) 'undefined)
;;;(test '(let ((x 123)) (let ((y (set! x (let ((u (set! x 456))) 789)))) x)) 789)

;;; SCHEME ERROR when setting before init
;;; (test '(letrec ((x (let ((u (set! x 123))) 456))) x) 456)