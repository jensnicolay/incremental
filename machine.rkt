#lang racket
(require racket/hash)
(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")

(provide compile conc-eval type-eval parameterize-full-debug!)
(random-seed 111)

;;;;;;;;;;
(define debug-print-in #f)
(define debug-print-out #f)
(define debug-print #f)
(define output-graph #f)
;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)

(struct state (e κ) #:transparent)
(struct root (e s) #:transparent)
(struct obj (e s) #:transparent)

(struct system (graph end-state parent) #:transparent)
(struct graph (fwd bwd initial) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(graph ~v :initial ~v)" (graph-fwd v) (graph-initial v))))

(define compile (make-compiler))

(define (successors s g)
  (hash-ref (graph-fwd g) s (set)))

(define (predecessors s g)
  (hash-ref (graph-bwd g) s (set)))

(define (points-to? s s* g)
  (set-member? (hash-ref (graph-fwd g) s (set)) s*))

; (define (graph-has-node? g s)
;   (or (hash-has-key? (graph-fwd g) s)
;       (hash-has-key? (graph-bwd g) s)))

(define (explore e0 lat kalloc)

  (define α (lattice-α lat)) 
  (define γ (lattice-γ lat))
  (define ⊥ (lattice-⊥ lat))
  ; (define ⊑ (lattice-⊑ lat))
  (define ⊔ (lattice-⊔ lat))
  (define true? (lattice-true? lat))
  (define false? (lattice-false? lat))
  ; (define α-eq? (lattice-eq? lat))
  (define Prims-lat (lattice-global lat))

  
  (define s0 (state e0 'κ0))

  (define Compiled-prims (hash))
  (define Parent-prim (hash))

  ; (define (define-value-prim! x proc)
  ;   (set! Value-prims (hash-set Value-prims x proc)))

  (define (define-compile-prim! x e-lam)
    (let ((e (compile e-lam)))
      (set! Parent-prim (hash-union Parent-prim (parent-map e)))
      (set! Compiled-prims (hash-set Compiled-prims x (obj e s0)))))

  (include "primitives.rkt")

  (define Parent (hash-union Parent-prim (parent-map e0)))
  (for ((obj (in-hash-values Compiled-prims)))
    (let ((e-lam (obj-e obj)))
      (set! Parent (hash-set Parent e-lam e0))))
  
  (define g (graph (hash) (hash) #f))
  
  (define (add-transitions! from To)
    (match-let (((graph fwd bwd _) g))
      (set! g (graph (hash-set fwd from (set-union (hash-ref fwd from (set)) To))
                      (for/fold ((bwd bwd)) ((to (in-set To)))
                        (hash-set bwd to (set-add (hash-ref bwd to (set)) from)))
                      #f))))

  (define (body-expression? e)
    («lam»? (parent e)))

  (define (parent e)
    (hash-ref Parent e #f))


  ; because this cache is global (and not specific to a `ge` call), it needs to be maintained (cleared!) when needed!
  (define ecache (hash))

  ; remember: `ge` never causes graph updates (does not invoke `step`)
  (define (graph-eval e s) ; general TODO: every fw movement should be restrained to previous path(s)
    (and debug-print-in (debug-print-in "#~v: graph-eval ~v" (state->statei s) (ast->string e)))
    ;(prompt "graph-eval")

    (let ((key (cons e s)))
      (if (hash-has-key? ecache key)
          (let ((d-result (hash-ref ecache key)))
            (and debug-print-out (debug-print-out "#~v: graph-eval ~v: [from cache] ~a" (state->statei s) (ast->string e) (user-print d-result)))
            d-result)
          (begin
            (set! ecache (hash-set ecache key ⊥))
            (let ((d-result
                (match e
                  ((«lit» _ d)
                    (α d))
                  ((«id» _ x)
                    (for/fold ((d ⊥)) ((r (in-set (lookup-var-root x s))))
                      (⊔ d (if r
                                (eval-var-root x r s)
                                (or (hash-ref Prims-lat x #f) ; by doing this check here, and not using e-var-root for unbound stuff, prims cannot be redefined
                                    (hash-ref Compiled-prims x #f)
                                    (error "unbound variable" x))))))
                  ((«lam» _ _ _)
                    (α (obj e s)))
                  ((«quo» _ d)
                    (α d))
                  ((«let» _ _ _ e-body)
                    (let ((s* (state e-body (state-κ s))))
                      (graph-eval e-body s*)))
                  ((«letrec» _ _ _ e-body)
                    (let ((s* (state e-body (state-κ s))))
                      (graph-eval e-body s*)))
                  ((«if» _ _ _ _)
                    (let ((S-succ (successors s g)))
                      (for/fold ((d-result ⊥)) ((s* (in-set S-succ)))
                        (⊔ d-result (graph-eval (state-e s*) s*)))))
                  ((«set!» _ _ _)
                    (α '<unspecified>))
                  ((«app» _ e-rator e-rands) ; possible logic: check for 0 or 1+ compound apps
                    (let ((d-compound
                        (for/fold ((d ⊥)) ((s-succ (in-set (successors s g))))
                          (match s-succ
                            ((state (? (lambda (e) (body-expression? e)) e-body) _)
                              (⊔ d (graph-eval e-body s-succ)))
                            (_
                              d)))))
                      (let ((d-prim
                          (let ((d-proc (graph-eval e-rator s)))
                            (for/fold ((d ⊥)) ((proc (in-set (γ d-proc))))
                              (match proc
                                ((prim2 _ proc)
                                  (let ((d-rands (map (lambda (e-rand) (graph-eval e-rand s)) e-rands))) ; TODO fix multiple evals for multiple prims
                                    (⊔ d (apply proc d-rands))))
                                (_
                                  d)
                              )))))
                        (⊔ d-compound d-prim))))
                  ((«cons» _ _ _)
                    (α (obj e s)))
                  ((«car» _ e-id)
                    (let ((R (lookup-path-root e-id 'car s)))
                      (for/fold ((d ⊥)) ((r (in-set R)))
                        (⊔ d (eval-path-root r s)))))
                  ((«cdr» _ e-id)
                    (let ((R (lookup-path-root e-id 'cdr s)))
                      (for/fold ((d ⊥)) ((r (in-set R)))
                        (⊔ d (eval-path-root r s)))))
                  ((«make-vector» _ _ _)
                    (α (obj e s)))
                  ((«vector-ref» _ e-id e-index)
                    (let ((d-index (graph-eval e-index s)))
                      (let ((R (lookup-path-root e-id d-index s))) ; TODO subsumption of indices
                        (for/fold ((d ⊥)) ((r (in-set R)))
                          (⊔ d (eval-path-root r s))))))
                  )))
              (and debug-print-out (debug-print-out "#~v: graph-eval ~v: ~a" (state->statei s) (ast->string e) d-result))

              
              ; ; assert still in progress
              ; (unless (equal? (hash-ref ecache key) ⊥)
              ;   (error "assertion violated" (hash-ref ecache key)))

              ; update cache
              (set! ecache (hash-set ecache key d-result))
              
              d-result)))))

(define (lookup-var-root x s)
  (and debug-print-in (debug-print-in "#~v: lookup-var-root ~a" (state->statei s) x))

  (define (ast-helper W V R)
    (if (set-empty? W)
        R
        (let ((s (set-first W)))
          (if (set-member? V s)
              (ast-helper (set-rest W) V R)
              (let* ((e (state-e s))
                     (κ (state-κ s))
                     (pa (parent e)))
                ;(and debug-print (debug-print "#~v: ast-helper x ~v pa ~v" (state->statei s) x (and pa (ast->string pa))))
                (match pa
                  ((«let» _ («id» _ (== x)) (and (not (== e)) e-init) _)
                    (ast-helper (set-rest W) (set-add V s) (set-add R (root e-init (state e-init κ))))) ; successor state exists because of `step`
                  ((«letrec» _ («id» _ (== x)) e-init _)
                    (ast-helper (set-rest W) (set-add V s) (set-add R (root e-init (state e-init κ))))) ; successor state exists because of `step`
                  ((«lam» _ (list xs ...) _) ; s evals body exp e
                    (let ((S* (predecessors s g))) 
                      (let pred-loop ((S* S*) (W (set-rest W)) (R R))
                        (if (set-empty? S*)
                            (ast-helper W (set-add V s) R)
                            (let ((s* (set-first S*))) ; s* is application of compound
                              (if (set-member? V s*)
                                  (pred-loop (set-rest S*) W R)
                                  (match s*
                                    ((state («app» _ e-rator e-args) _)
                                      (let param-args-loop ((xs xs) (e-args e-args))
                                        (if (null? xs)
                                            (let ((d-clo (graph-eval e-rator s*)))
                                              (let clo-loop ((Clo (γ d-clo)) (W W) (R R))
                                                (if (set-empty? Clo)
                                                    (pred-loop (set-rest S*) W R)
                                                    (let ((cl (set-first Clo)))
                                                      (match cl
                                                        ((obj _ s**) ; s** is where closure was created
                                                          ;((debug-print) "found closure: ~v" d-clo)
                                                          (clo-loop (set-rest Clo) (set-add W s**) R))
                                                        (_
                                                          (clo-loop (set-rest Clo) W (set-add R #f)))))))) ; prim (in prim?)
                                            (let ((e-decl (car xs)))
                                              (match e-decl
                                                  ((«id» _ (== x))
                                                    (pred-loop (set-rest S*) W (set-add R (root (car e-args) s*))))
                                                  (_
                                                    (param-args-loop (cdr xs) (cdr e-args)))))))))))))))
                  ((«lam» _ («id» _ (== x)) _) 
                    (let ((R
                        (for/fold ((R R)) ((s* (in-set (predecessors s g))))
                          (match s*
                            ((state («app» l e-rator e-args) _)
                              (let ((e-list (let loop ((e-args e-args))
                                              (if (null? e-args)
                                                  («lit» (- l) '())
                                                  (let ((e-arg (car e-args)))
                                                    (let ((l (ast-label e-arg)))
                                                      («cons» (- l) e-arg (loop (cdr e-args)))))))))
                                (set-add R (root e-list s*))))))))
                        (ast-helper (set-rest W) (set-add V s) R)))
                  (#f (ast-helper (set-rest W) (set-add V s) (set-add R #f))) ; no parent = no var-root found
                  (_
                    (ast-helper (set-add (set-rest W) (state pa κ)) (set-add V s) R)
                  )))))))

            (let ((R (ast-helper (set s) (set) (set))))
              (and debug-print-out (debug-print-out "#~v: lookup-var-root ~a: ~v" (state->statei s) x (user-print R)))
              R))

(define (eval-var-root x r s) ; the `x` param is optimization (see below)
  (and debug-print-in (debug-print-in "#~v: eval-var-root ~a" (state->statei s) (user-print r)))
  
  (match-let (((root e-r s-r) r)) 

  (define (eval-var-root-helper W V d)
      (if (set-empty? W)
          d
          (let ((s (set-first W)))
            ;(and debug-print (debug-print "#~v: eval-var-root-helper r ~a" (state->statei s) (user-print r)))
            (if (set-member? V s)
                (eval-var-root-helper (set-rest W) V d)
                (match s
                  ((== s-r)
                    (eval-var-root-helper (set-rest W) (set-add V s) (⊔ d (graph-eval e-r s-r))))
                  ((state e κ)
                  (match e
                      ((«set!» _ («id» _ (== x)) e-update) ; `== x` avoids looking up var-roots for different name (which can never match `b` anyway)
                        (let root-loop ((R (lookup-var-root x s)) (W (set-rest W)) (d ⊥))
                          (if (set-empty? R)
                              (eval-var-root-helper W (set-add V s) d)
                              (let ((r* (set-first R)))
                                (if (equal? r r*)
                                    (root-loop (set-rest R) W (⊔ d (graph-eval e-update s)))
                                    (root-loop (set-rest R) (set-union W (predecessors s g)) d))))))
                      (_
                        (eval-var-root-helper (set-union (set-rest W) (predecessors s g)) (set-add V s) d))
                      ))
                    )))))

  (let ((d (eval-var-root-helper (predecessors s g) (set) ⊥)))
    (and debug-print-out (debug-print-out "#~v: eval-var-root ~a: ~a" (state->statei s) (user-print r) (user-print d)))
    d)))

(define (lookup-path-root e-id f s)   
  (and debug-print-in (debug-print-in "#~v: lookup-path-root ~a ~a" (state->statei s) (ast->string e-id) f))

  (let ((R
    (let ((d (graph-eval e-id s)))
      (let d-loop ((D (γ d)) (R (set)))
        (if (set-empty? D)
            R
            (let ((d (set-first D)))
              (match* (d f)
                (((obj («cons» _ e-car _) s-root) 'car)
                  (d-loop (set-rest D) (set-add R (root e-car s-root))))
                (((obj («cons» _ _ e-cdr) s-root) 'cdr)
                  (d-loop (set-rest D) (set-add R (root e-cdr s-root))))
                ;;
                (((obj («make-vector» _ e-size e) s-root) e-index)
                  (d-loop (set-rest D) (set-add R (root (cons e f) s-root))))
              )))))))
    (and debug-print-out (debug-print-out "#~v: lookup-path-root ~a ~a: ~a" (state->statei s) (ast->string e-id) f R))
    R))

(define (eval-path-root r s) ; what if we keep field-name (quicker lookup distinction)
  (and debug-print-in (debug-print-in "#~v: eval-path-root ~a" (state->statei s) (user-print r)))
  
  (let
    ((s-r (root-s r)))

    (define (eval-path-root-helper W V d)
      (if (set-empty? W)
          d
          (let ((s (set-first W)))
            ;(and debug-print (debug-print "#~v: eval-path-root-helper r ~a" (state->statei s) (user-print r)))
            (if (set-member? V s)
                (eval-path-root-helper (set-rest W) V d)
                (match s
                  ((== s-r)
                    (match r
                      ((root (cons e-r f) s-r)
                        (eval-path-root-helper (set-rest W) (set-add V s) (⊔ d (graph-eval e-r s-r))))
                      ((root e-r s-r)
                        (eval-path-root-helper (set-rest W) (set-add V s) (⊔ d (graph-eval e-r s-r))))))
                  ((state e κ)
                    (match e
                      ((«set-car!» _ e-id e-update)
                        (let root-loop ((R (lookup-path-root e-id 'car s)) (W (set-rest W)) (d ⊥))
                          (if (set-empty? R)
                              (eval-path-root-helper W (set-add V s) d)
                              (let ((r* (set-first R)))
                                (if (equal? r r*)
                                  (root-loop (set-rest R) W (⊔ d (graph-eval e-update s)))
                                  (root-loop (set-rest R) (set-union W (predecessors s g)) d))))))
                      ((«set-cdr!» _ e-id e-update)
                        (let root-loop ((R (lookup-path-root e-id 'cdr s)) (W (set-rest W)) (d ⊥))
                          (if (set-empty? R)
                              (eval-path-root-helper W (set-add V s) d)
                              (let ((r* (set-first R)))
                                (if (equal? r r*)
                                  (root-loop (set-rest R) W (⊔ d (graph-eval e-update s)))
                                  (root-loop (set-rest R) (set-union W (predecessors s g)) d))))))
                      ((«vector-set!» _ e-id e-index e-update)
                        (let ((d-index (graph-eval e-index s))) ; could be used to avoid looking up path root (if index ≠)
                          (let root-loop ((R (lookup-path-root e-id d-index s)) (W (set-rest W)) (d ⊥))
                            (if (set-empty? R)
                                (eval-path-root-helper W (set-add V s) d)
                                (let ((r* (set-first R)))
                                  (if (equal? r r*)
                                    (root-loop (set-rest R) W (⊔ d (graph-eval e-update s)))
                                    (root-loop (set-rest R) (set-union W (predecessors s g)) d)))))))
                      (_
                        (eval-path-root-helper (set-union (set-rest W) (predecessors s g)) (set-add V s) d))
                      ))
                  )))))

    (let ((d (eval-path-root-helper (predecessors s g) (set) ⊥)))
      (and debug-print-out (debug-print-out "#~v: eval-path-root ~a: ~v" (state->statei s) (user-print r) d))
      d)))

  (define (cont s)
    (and debug-print-in (debug-print-in "#~v: cont" (state->statei s)))

    (define (cont-helper W V S-kont)
      (if (set-empty? W)
          S-kont
          (let ((eκ (set-first W))) ; not all e+kappa combos are states
            (if (set-member? V eκ)
                (cont-helper (set-rest W) V S-kont)
                (match-let (((cons e κ) eκ))
                  (let ((p (parent e)))
                    ;((debug-print) "cont e ~v κ ~v p ~v" e κ p)
                    (match p
                      ((«let» _ _ (== e) e-body)
                        (cont-helper (set-rest W) (set-add V eκ) (set-add S-kont (state e-body κ))))
                      ((«letrec» _ _ (== e) e-body)
                        (cont-helper (set-rest W) (set-add V eκ) (set-add S-kont (state e-body κ))))
                      ((«lam» _ _ _) ;((«lam» _ _ (== e)) always holds because of parent
                        (if (parent p) ; for prims!
                            (begin
                              ;((debug-print) "pred of #~v is ~v" (state->statei (state e κ)) (user-print (predecessor (state e κ) g)))
                              (let ((S-pred (predecessors (state e κ) g)))
                                (cont-helper (set-union (set-rest W) (for/set ((s-pred (in-set S-pred))) (cons (state-e s-pred) (state-κ s-pred)))) (set-add V eκ) S-kont)))
                            (cont-helper (set-rest W) (set-add V eκ) S-kont))) ; 'unconnected' prim lam
                      (#f
                        (cont-helper (set-rest W) (set-add V eκ) S-kont))
                      (_
                        (cont-helper (set-add (set-rest W) (cons p κ)) (set-add V eκ) S-kont))
                      )))))))

    (let ((S-kont (cont-helper (set (cons (state-e s) (state-κ s))) (set) (set))))
      (and debug-print-out (debug-print-out "#~v: cont: ~a" (state->statei s) S-kont))
      S-kont))

  (define (step s)
    (and debug-print (debug-print "#~v: step ~a" (state->statei s) (ast->string (state-e s))))
    (let ((S-succ
        (match-let (((state e κ) s))
          (match e
            ((«let» _ _ init _)
              (set (state init κ)))
            ((«letrec» _ _ init _)
              (set (state init κ)))
            ((«if» _ e-cond e-then e-else)
              (let ((d-cond (graph-eval e-cond s)))
                (set-union
                  (if (true? d-cond) (set (state e-then κ)) (set))
                  (if (false? d-cond) (set (state e-else κ)) (set)))))

            ((«app» _ («id» _ "display") e-rands)
              (printf "DISPDEB: ~a ~a\n" (graph-eval (car e-rands) s) (- (current-milliseconds) explore-start-time))
              (cont s))

            ((«app» _ e-rator e-rands)
              (let ((D-proc (γ (graph-eval e-rator s))))
                (let d-proc-loop ((D-proc D-proc) (S-succ (set)))
                  (if (set-empty? D-proc)
                      S-succ
                      (let ((d-proc (set-first D-proc)))
                        (match d-proc
                          ((obj («lam» _ _ e-body) _)
                            (let ((κ* (kalloc e d-proc)))
                              (let ((s* (state e-body κ*)))
                                (d-proc-loop (set-rest D-proc) (set-add S-succ s*)))))
                          ((prim2 _ _)
                            (d-proc-loop (set-rest D-proc) (set-union S-succ (cont s))))
                          (_
                            (d-proc-loop (set-rest D-proc) S-succ))
                        ))))))
            (_ (cont s))
          ))))
    (and debug-print (debug-print "#~v: step: ~a" (state->statei s) (set-map S-succ state->statei)))
    S-succ))

  (define (explore! W V S-end)
    (if (set-empty? W)
        S-end
        (let ((s (set-first W)))
          (if (set-member? V s)
              (explore! (set-rest W) V S-end)
              (let ((S-succ (step s)))
                (if (set-empty? S-succ) ; end state!
                    (explore! (set-rest W) (set-add V s) (set-add S-end s))
                    (let ((W* (set-union (set-rest W) S-succ)))
                      (let succ-loop ((W-succ S-succ))
                        (if (set-empty? W-succ)
                            (begin
                              (add-transitions! s S-succ)
                              (explore! W* (set-add V s) S-end))
                            (let ((s* (set-first W-succ)))
                              (if (set-member? V s*) ; loop to visited state     
                                (begin                 
                                  (and debug-print (debug-print "LOOP: #~v -> #~v" (state->statei s) (state->statei s*)))
                                  (if (points-to? s s* g) ; if already in graph
                                      (begin
                                        (and debug-print (debug-print "LOOP already in graph: #~v -> #~v" (state->statei s) (state->statei s*)))
                                        (succ-loop (set-rest W-succ))
                                      )
                                      (begin ; break!
                                        (and debug-print (debug-print "LOOP NOT already in graph: #~v -> #~v" (state->statei s) (state->statei s*)))
                                        (add-transitions! s S-succ)
                                        (set! ecache (hash-clear ecache))
                                        (explore! W* (set) S-end)))
                                )
                                (succ-loop (set-rest W-succ)))))))))))))

  (define explore-start-time (current-milliseconds))
  (define S-end (explore! (set s0) (set) (set)))
  (define explore-time (- (current-milliseconds) explore-start-time))

  (and debug-print (debug-print "EXPLORED ~v -> ~v in ~a ms" (state->statei s0) (set-map S-end state->statei) explore-time))
  (and output-graph (generate-dot (graph (graph-fwd g) (graph-bwd g) s0) "grapho"))

  (define (dispatcher msg)
    (match msg
      (`(graph) (graph (graph-fwd g) (graph-bwd g) s0))
      (`(S-end) S-end)
      (`(evaluate)
          (for/fold ((d ⊥)) ((s-end (in-set S-end)))
            (⊔ d (graph-eval (state-e s-end) s-end))))
    ))
  
  dispatcher)
      
(define conc-kalloc
    (let ((counter 0))
      (lambda (e-app d-proc)
        (begin
          (set! counter (add1 counter))
          counter))))

(define (conc-eval e)
  ((explore e conc-lattice conc-kalloc) `(evaluate)))

(define (type-kalloc e-app d-proc)
  d-proc)
  
(define (type-eval e)
  ((explore e type-lattice type-kalloc) `(evaluate)))

;;; OUTPUT STUFF
(define (parameterize-full-debug!)
  (define debug-print-level 0)
  (set! debug-print-in 
    (lambda args
      (apply debug-print args)
      (set! debug-print-level (add1 debug-print-level))))
  (set! debug-print-out
    (lambda args
      (set! debug-print-level (sub1 debug-print-level))
      (apply debug-print args)))
  (set! debug-print
    (lambda args
      (for ((i debug-print-level))
        (display " "))
      (apply printf args)
      (newline))))

(define (output-graph!)
  (set! output-graph #t))

(define (user-print d)
  (match d
    ((obj e s) (format "(obj ~a ~a)" (user-print e) (user-print s)))
    ((state e κ) (format "#~v" (state->statei d)))
    ((root (cons e f) s) (format "(root (~a ~a) ~a)"(ast->string e) f (user-print s)))
    ((root e s) (format "(root ~a ~a)"(ast->string e) (user-print s)))
    ((? ast?) (format "@~a" (ast-label d)))
    ((? set?) (format "{~a}" (set-map d user-print)))
    ((cons aa dd) (format "(~a ~a)" (user-print aa) (user-print dd)))
    (_ d)))

(define (index v x)
  (let ((i (vector-member x v)))
    (if i
        i
        (let ((i (add1 (vector-ref v 0))))
          (vector-set! v 0 i)
          (vector-set! v i x)
          i))))
(define stateis (make-vector 4096))
(define (state->statei q) (index stateis q))

(define (state-repr s)
  (format "~a | ~a" (ast->string (state-e s)) (user-print (state-κ s))))

(define (generate-dot g name)
  (let ((dotf (open-output-file (format "~a.dot" name) #:exists 'replace)))
  
    (define (dot-helper s S-seen)
      (let ((si (state->statei s)))
        (fprintf dotf "~a [label=\"~a | ~a\"];\n" si si (state-repr s))
        (let ((S-succ (successors s g)))
          (for ((s* (in-set S-succ)))
            (let ((si* (state->statei s*)))
              (fprintf dotf "~a -> ~a;\n" si si*)
              (unless (set-member? S-seen s*)
                (dot-helper s* (set-add S-seen s*))))))))
    
    (fprintf dotf "digraph G {\n")
    (let ((s0 (graph-initial g)))
      (dot-helper s0 (set))
      (fprintf dotf "}")
      (close-output-port dotf))))

;;; TESTS

(module+ main
 ;(parameterize-full-debug!)
 ;(output-graph!) 

 (define e (compile (file->value "test/primtest.scm")))

 (let ((start-time (current-milliseconds)))
  (let ((result (type-eval e)))
    (let ((end-time (- (current-milliseconds) start-time)))
      (printf "~a\n~a ms\n" result end-time)))))
