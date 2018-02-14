#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")

(define ns (make-base-namespace))

;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)
(struct clo (e) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<clo ~v>" (clo-e v))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))
(struct addr (a) #:transparent)
(struct binding (e κ) #:transparent)
(struct ctx (e d-proc n) #:transparent ; (e-app d-proc n)
 #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<ctx ~v ~v>" (ctx-e v) (ctx-n v))))
(struct state (e κ) #:transparent)
(struct system (graph parent) #:transparent)
(struct graph (fwd bwd initial) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(graph ~v :initial ~v)" (graph-fwd v) (graph-initial v))))


(define count!
  (let ((counter 0))
    (lambda ()
      (begin0
        counter
        (set! counter (add1 counter))))))


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
  (let ((dotf (open-output-file (format "~a.dot" name) #:exists 'replace))
        (fwd (graph-fwd g)))
    (fprintf dotf "digraph G {\n")
    (for/fold ((S (set))) (((s S-succ) fwd))
      (let ((si (state->statei s)))
        (unless (set-member? S si)
          (fprintf dotf "~a [label=\"~a | ~a\"];\n" si si (state-repr s)))
        (for/fold ((S (set-add S si))) ((s* S-succ))
          (let ((si* (state->statei s*)))
            (unless (set-member? S si*)
              (fprintf dotf "~a [label=\"~a | ~a\"];\n" si* si* (state-repr s*)))
            (fprintf dotf "~a -> ~a;\n" si si*)
            (set-add S si*)))))
    (fprintf dotf "}")
    (close-output-port dotf)))

;;;

(define (successors s g)
  (hash-ref (graph-fwd g) s (set)))

(define (predecessors s g)
  (hash-ref (graph-bwd g) s (set)))

(define (state-exists? s g)
  (hash-ref (graph-fwd g) s #f))

(define (ev e s g lat parent) ; general TODO: every fw movement should be restrained to previous path(s)
  (printf "ev ~v in ~v\n" e s)
  (match e
    ((«lit» _ d)
     (printf "-> ~v\n" ((lattice-α lat) d))
     ((lattice-α lat) d))
    ((«id» _ x)
     (let ((d (lookup-variable x s g lat parent)))
       (printf "-> ~v\n" d)
       d))
    ((«lam» _ _ _)
     (printf "-> clo ~v\n" e)
     ((lattice-α lat) (clo e)))
    ((«let» _ _ _ e-body)
     (let graph-fw ((W (successors s g)) (S (set)) (d (lattice-⊥ lat)))
       (if (set-empty? W)
           d
           (let ((s* (set-first W)))
             (if (set-member? S s*)
                 (graph-fw (set-rest W) S d)
                 (match s*
                   ((state (== e-body) (== (state-κ s)))
                    (graph-fw (set-rest W) (set-add S s*) ((lattice-⊔ lat) d (ev e-body s* g lat parent))))
                   (_
                    (graph-fw (set-union W (successors s* g)) (set-add S s*) d))))))))
    ((«if» _ _ _ _)
     (let graph-succ ((W (successors s g)) (d (lattice-⊥ lat)))
       (if (set-empty? W)
           d
           (let ((s* (set-first W)))
             (graph-succ (set-rest W) ((lattice-⊔ lat) d (ev (state-e s*) s* g lat parent)))))))
    ((«app» _ («id» _ x) e-rands)
     (let ((κ (state-κ s)))
       (let ((S-succ (successors s g)))
         (let loop ((W S-succ) (d (lattice-⊥ lat)) (prim (set-empty? S-succ)))
           (if (set-empty? W)
               (if prim
                   (let ((d-rands (map (lambda (e-rand) (ev e-rand s g lat parent)) e-rands))
                         (proc (let ((prim-cons (assoc x (lattice-global lat))))
                                   (match prim-cons
                                     ((cons _ (prim2 _ proc))
                                      proc)))))
                     (printf "~v: primitive app ~v on ~v\n" e x d-rands)
                     (let ((d* (apply proc d-rands)))
                       ((lattice-⊔ lat) d d*)))
                   d)
               (let ((s* (set-first W)))
                 (match s*
                   ((state e-body (ctx (== e) _ _))
                    (printf "\t~v: compound app with body ~v\n" e e-body)
                    (loop (set-rest W) ((lattice-⊔ lat) d (ev e-body s* g lat parent)) prim))
                   (_
                    (loop (set-rest W) d #t)))))))))))

(define (lookup-static x s g lat parent)
  (printf "lookup-static ~v ~v\n" x s)

  (define (ast-helper e κ)
    (let ((pa (parent e)))
      (printf "ast-helper ~v e ~v pa ~v\n" x e pa)
      (match pa
        ((«let» _ _ (== e) _)
         (ast-helper pa κ))
        ((«let» _ (and e-decl («id» _ (== x))) _ _)
         (set (binding e-decl κ)))
        ((«let» _ _ _ _)
         (ast-helper pa κ))
        ((«letrec» _ (and e-decl («id» _ (== x))) _ _)
         (set (binding e-decl κ)))
        ((«letrec» _ _ _ _)
         (ast-helper pa κ))
        ((«app» _ _ _)
         (ast-helper pa κ))
        ((«if» _ _ _ _)
         (ast-helper pa κ))
        ((«lam» _ (list xs ...) _)
         (let param-loop ((xs xs))
           (if (null? xs)
               (find-lambda pa s (set))
               (let ((e-decl (car xs)))
                 (match e-decl
                   ((«id» _ (== x))
                    (set (binding e-decl κ)))
                   (_
                    (param-loop (cdr xs))))))))
        (#f (set (binding («id» -1 x) 'unbound))) ; no static decl found: keep prim name `x`
        (_ (error "cannot handle expression" pa)))))

  (define (find-lambda e-lam s S)
    (printf "find-lambda ~v ~v\n" e-lam s)
    (let loop ((W (predecessors s g)) (S S) (res (set)))
      (if (set-empty? W)
          res
          (let ((s (set-first W)))
            (printf "lam ~v\n" s)
            (match s
              ((state (== e-lam) κ)
               (printf "found lam ~v => ~v\n" e-lam s)
               (loop (set-rest W) (set-add S s) (set-union res (ast-helper e-lam κ))))
              ((state («let» _ _ (== e-lam) _) κ)
               (printf "found lam ~v => ~v\n" e-lam s)
               (loop (set-rest W) (set-add S s) (set-union res (ast-helper e-lam κ))))
              ((state («letrec» _ _ (== e-lam) _) κ)
               (printf "found lam ~v => ~v\n" e-lam s)
               (loop (set-rest W) (set-add S s) (set-union res (ast-helper e-lam κ))))
              (_ (loop (set-union (set-rest W) (predecessors s g)) (set-add S s) res)))))))
  
  (let ((res (ast-helper (state-e s) (state-κ s))))
    (printf "looked up static ~v = ~v\n" x res)
    res))

(define (lookup-dynamic β s g lat parent)
  (printf "lookup-dynamic ~v ~v\n" β s)

  (match-let (((binding («id» _ x) κ-β) β))
    (let loop ((W (set s)) (S (set)) (d (lattice-⊥ lat)))
      (if (set-empty? W)
          d
          (let ((s (set-first W)))
            (if (set-member? S s)
                (loop (set-rest W) S d)
                (let ((prs (predecessors s g)))
                  (if (set-empty? prs)
                      (let ((prim-cons (assoc x (lattice-global lat))))
                        (match prim-cons
                          ((cons _ d-prim)
                           (loop (set-rest W) (set-add S s) ((lattice-⊔ lat) d d-prim)))
                          (#f
                           (error "unbound variable ~v" x))))
                      (let prs-loop ((prs prs) (W (set-rest W)) (d d))
                        (if (set-empty? prs)
                            (loop W (set-add S s) d)
                            (let ((s-pr (set-first prs)))
                              (match s-pr
                                ((state e κ)
                                 (printf "dyn ~v\n" s-pr)
                                 (match e
                                   ((«lit» _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«lam» _ _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«let» _ («id» _ (== x)) e-init _)
                                    (if (equal? κ κ-β)
                                        (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-init s-pr g lat parent)))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ((«let» _ _ (and e-app («app» _ _ _)) _)
                                    (if (and (equal? e-app (ctx-e (state-κ s))) ; s-pr is compound call, s is proc entry
                                             (equal? (state-κ s) κ-β))
                                        (let* ((e-proc (clo-e (ctx-d-proc (state-κ s))))
                                               (xs («lam»-x e-proc)))
                                          (let param-loop ((xs xs) (e-args («app»-aes e-app)))
                                            (if (null? xs)
                                                (prs-loop (set-rest prs) (set-add W s-pr) d)
                                                (if (equal? («id»-x (car xs)) x)
                                                    (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev (car e-args) s-pr g lat parent)))
                                                    (param-loop (cdr xs) (cdr e-args))))))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ((«let» _ _ _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«letrec» _ («id» _ (== x)) e-init _)
                                    (if (equal? κ κ-β)
                                        (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-init s-pr g lat parent)))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ((«letrec» _ _ (and e-app («app» _ _ _)) _)
                                    (if (and (equal? e-app (ctx-e (state-κ s))) ; s-pr is compound call, s is proc entry
                                             (equal? (state-κ s) κ-β))
                                        (let* ((e-proc (clo-e (ctx-d-proc (state-κ s))))
                                               (xs («lam»-x e-proc)))
                                          (let param-loop ((xs xs) (e-args («app»-aes e-app)))
                                            (if (null? xs)
                                                (prs-loop (set-rest prs) (set-add W s-pr) d)
                                                (if (equal? («id»-x (car xs)) x)
                                                    (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev (car e-args) s-pr g lat parent)))
                                                    (param-loop (cdr xs) (cdr e-args))))))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ((«letrec» _ _ _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«id» _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«if» _ _ _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«app» _ _ _)
                                    (if (and (equal? e (ctx-e (state-κ s))) ; s-pr is compound call, s is proc entry
                                             (equal? (state-κ s) κ-β))
                                        (let* ((e-proc (clo-e (ctx-d-proc (state-κ s))))
                                               (xs («lam»-x e-proc)))
                                          (let param-loop ((xs xs) (e-args («app»-aes e)))
                                            (if (null? xs)
                                                (prs-loop (set-rest prs) (set-add W s-pr) d)
                                                (if (equal? («id»-x (car xs)) x)
                                                    (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev (car e-args) s-pr g lat parent)))
                                                    (param-loop (cdr xs) (cdr e-args))))))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ))
                                ))))))))))))
    
  
(define (lookup-variable x s g lat parent)
  (printf "lookup-variable ~v ~v\n" x s)
  (let loop ((W (lookup-static x s g lat parent)) (d (lattice-⊥ lat)))
    (if (set-empty? W)
        d
        (loop (set-rest W) ((lattice-⊔ lat) d (lookup-dynamic (set-first W) s g lat parent))))))

(define (explore e lat)

  (define ast (compile e))
  (define parent (make-parent ast))
  
  ; state -> (set state...)
  (define fwd (hash))
  (define bwd (hash))
  
  ;(define Ξ (hash #f (set)))
  ;(define Ξi 0)

  (define Δi 0)
  
  (define α (lattice-α lat))
  (define γ (lattice-γ lat))
  (define ⊥ (lattice-⊥ lat))
  (define ⊑ (lattice-⊑ lat))
  (define ⊔ (lattice-⊔ lat))
  (define true? (lattice-true? lat))
  (define false? (lattice-false? lat))
  (define α-eq? (lattice-eq? lat))


  ;(define (add-transition graph from to)
  ;  (hash-set graph from (set-add (hash-ref graph from (set)) to)))

  ;(define (add-transition! from to)
  ;  (set! graph (add-transition graph from to)))

  (define (add-transitions! from tos)
    (set! fwd (hash-set fwd from (set-union (hash-ref fwd from (set)) tos)))
    (set! bwd (for/fold ((bwd bwd)) ((to (in-set tos)))
                (hash-set bwd to (set-add (hash-ref bwd to (set)) from)))))
     
  (define (stack-pop s)
    (match s
      ((state _ κ)
       (let ((e-app (ctx-e κ)))
         (let graph-bw ((W (hash-ref bwd s)) (S (set)) (κs (set)))
           (if (set-empty? W)
               κs
               (let ((s (set-first W)))
                 (printf "popping ~v\n" s)
                 (if (set-member? S s)
                     (graph-bw (set-rest W) S κs)
                     (match s
                       ((state (== e-app) κ*)
                        (graph-bw (set-rest W) (set-add S s) (set-add κs (state-κ s))))
                       ((state («let» _ _ (== e-app) _) κ*)
                        (graph-bw (set-rest W) (set-add S s) (set-add κs (state-κ s))))
                       (_
                        (graph-bw (set-union (set-rest W) (hash-ref bwd s (set))) (set-add S s) κs)))))))))))
               
      
  (define (cont e κ)
    (printf "cont e ~v κ ~v\n" e κ)
    (let ((p (parent e)))
      (match p
        ((«let» _ _ _ (== e))
         (cont p κ))
        ((«let» _ _ (== e) e-body)
         (set (state e-body κ)))
        ((«letrec» _ _ _ (== e))
         (cont p κ))
        ((«letrec» _ _ (== e) e-body)
         (set (state e-body κ)))
        ((«if» _ _ (== e) _)
         (cont p κ))
        ((«if» _ _ _ (== e))
         (cont p κ))
        ((«lam» _ _ (== e))
         (let ((κs (stack-pop (state e κ))))
           (printf "pop e ~v κ ~v = ~v\n" e κ κs)
           (for/fold ((S-succ (set))) ((κ* (in-set κs)))
             (set-union S-succ (cont (ctx-e κ) κ*)))))
        (#f (set)))))
  
  (define (step s)
    (printf "\n#~v\nstep ~v\n" (state->statei s) s)

    (define (helper e κ)
      (match e
        ((? ae? e)
         (cont e κ))
        ((«let» _ _ init _)
         (helper init κ))
        ((«letrec» _ _ init _)
         (helper init κ))
        ((«if» _ e-cond e-then e-else)
         (let* ((g (graph fwd bwd #f))
                (d-cond (ev e-cond s g lat parent)))
           (set (state (if (true? d-cond) e-then e-else) κ))))
        ((«app» _ e-rator e-rands)
         (let* ((g (graph fwd bwd #f))
                (d-proc (ev e-rator s g lat parent)))
           (let loop ((W (γ d-proc)) (S-succ (set)))
             (if (set-empty? W)
                 S-succ
                 (match (set-first W)
                   ((clo («lam» _ _ e-body))
                    (let* ((κ* (ctx e d-proc (count!))) ; TODO ctxs hardcoded as concrete
                           (s* (state e-body κ*)))
                      (when (state-exists? s* g)
                        (set! Δi (add1 Δi)))
                      (loop (set-rest W) (set-add S-succ s*))))
                   ((clo («let» _ _ («lam» _ _ e-body) _))
                    (let* ((κ* (ctx e d-proc (count!))) ; TODO ctxs hardcoded as concrete
                           (s* (state e-body κ*)))
                      (when (state-exists? s* g)
                        (set! Δi (add1 Δi)))
                      (loop (set-rest W) (set-add S-succ s*))))
                   ((prim2 _ _)
                    (loop (set-rest W) (set-union S-succ (cont e κ)))))))))))

    (match s
      ((state e κ) (helper e κ))))

  (define (explore-loop W S)
    (if (set-empty? W)
        (system (graph fwd bwd ast) parent)
        (let ((s (set-first W)))
          (if (set-member? S s)
              (explore-loop (set-rest W) S)
              (let ((S* (set-add S s)))
                (let* ((Δi0 Δi)
                       (succs (step s))
                       (W* (set-union (set-rest W) succs))
                       (S* (if (> Δi Δi0)
                               (set)
                               (set-add S s))))
                  (printf "TRANS ~v -> ~v\n" (state->statei s) (set-map succs state->statei))
                  (add-transitions! s succs)
                  (explore-loop W* S*)))))))
    
  (explore-loop (set (state ast (ctx #f #f (count!)))) (set)))

(define (end-states g)
  (match g
    ((graph fwd _ _)
     (for/set (((from tos) (in-hash fwd)) #:when (set-empty? tos))
       from))))

(define (evaluate e lat)
  (let* ((sys (explore e lat))
         (g (system-graph sys))
         (S-end (end-states g))
         (parent (system-parent sys)))
    (printf "\n\nEXPLORED with end states ~v\n" (set-map S-end state->statei))
    (generate-dot g "grapho")
    (for/fold ((d (lattice-⊥ lat))) ((s (in-set S-end)))
      ((lattice-⊔ lat) d (ev (state-e s) s g lat parent)))))

(define (conc-eval e)
  (evaluate e conc-lattice))

;;; TESTS

(define (test e expected)
  (let ((result
            (with-handlers ((exn:fail?
                             (lambda (exc) (if (eq? expected 'FAIL)
                                             'FAIL
                                             (begin
                                               (printf "unexpected failure for ~a:\n" e)
                                               (raise exc))))))
              (conc-eval e))))
         (unless (equal? result expected)
           (error (format "wrong result for ~a:\n\texpected ~a\n\tgot      ~a" e expected result)))))

;(test '123 123)
;(test '(let ((x 10)) x) 10)
;(test '(let ((x 10)) (let ((y 20)) y)) 20)
;(test '(let ((x 10)) (let ((y 20)) x)) 10)
;(test '(let ((x 10)) (let ((x 20)) x)) 20)
;(test '(let ((x 123)) (let ((u (let ((x #f)) "dummy"))) x)) 123)
;
;(test '(+ 1 1) 2)
;(test '(let ((x (+ 1 1))) x) 2)
;(test '(let ((f (lambda () (- 5 3)))) (f)) 2)
;(test '(let ((f (lambda (x) (* x x)))) (f 4)) 16)
;(test '(let ((f (lambda (x) x))) (let ((v (+ 3 9))) v)) 12)
;(test '(let ((x 123)) (let ((f (lambda () x))) (f))) 123)
;(test '(let ((f (lambda (x) x))) (let ((v (f 999))) v)) 999)
;(test '(let ((g (lambda (v) v))) (let ((f (lambda (n) (let ((m (g 123))) (* m n))))) (f 2))) 246)
;(test '(let ((f (lambda (x) x))) (let ((u (f 1))) (f 2))) 2)
;(test '(let ((f (lambda (y) (let ((x y)) x)))) (let ((z (f "foo"))) (f 1))) 1)
;(test '(let ((f (lambda (x) (let ((v x)) v)))) (f 123)) 123)
;(test '(let ((f (lambda (x) (let ((i (lambda (a) a))) (i x))))) (let ((z1 (f 123))) (let ((z2 (f #t))) z2))) #t)
;
;(test '(if #t 1 2) 1)
;(test '(if #f 1 2) 2)
;(test '(if #t (+ 3 5) (- 4 6)) 8)
;(test '(if #f (+ 3 5) (- 4 6)) -2)
;(test '(let ((f (lambda (x) (* x x)))) (let ((v (f 4))) (if v (f 5) (f 6)))) 25)
;(test '(if #t (let ((x 1)) x) (let ((x 2)) x)) 1)
;(test '(if #f (let ((x 1)) x) (let ((x 2)) x)) 2)
;(test '(let ((x (if #t 1 2))) x) 1)
;(test '(let ((x (if #f 1 2))) x) 2)
;
;(test '(let ((f (lambda (x) (lambda (y) x)))) (let ((v (f 123))) (v 999))) 123)
;(test '(let ((f (lambda (x) (lambda (x) x)))) (let ((v (f 123))) (v 999))) 999)
;(test '(let ((f (lambda (g) (g 678)))) (let ((id (lambda (x) x))) (f id))) 678)
;(test '(let ((f (lambda (g x) (g x)))) (let ((id (lambda (x) x))) (f id 789))) 789)
;(test '(let ((f (lambda (g) (lambda (x) (g x))))) (let ((sq (lambda (x) (* x x)))) (let ((ff (f sq))) (ff 11)))) 121)

;
;(test '(letrec ((f (lambda (x) (if x "done" (f #t))))) (f #f)) "done")
;(test '(letrec ((f (lambda (x) (let ((v (= x 2))) (if v x (f (+ x 1))))))) (f 0)) 2)
;(test '(letrec ((fac (lambda (n) (let ((v (= n 0))) (if v 1 (let ((m (- n 1))) (let ((w (fac m))) (* n w)))))))) (fac 1)) 1)
;(test '(letrec ((fac (lambda (n) (let ((v (= n 0))) (if v 1 (let ((m (- n 1))) (let ((w (fac m))) (* n w)))))))) (fac 3)) 6)
;(test '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((n2 (- n 2))) (let ((f1 (fib n1))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 1)) 1)
;(test '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((f1 (fib n1))) (let ((n2 (- n 2))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 1)) 1)
;(test '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((n2 (- n 2))) (let ((f1 (fib n1))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 3)) 2)
;(test '(letrec ((fib (lambda (n) (let ((c (< n 2))) (if c n (let ((n1 (- n 1))) (let ((f1 (fib n1))) (let ((n2 (- n 2))) (let ((f2 (fib n2))) (+ f1 f2)))))))))) (fib 3)) 2)
;(test '(letrec ((count (lambda (n) (let ((t (= n 0))) (if t 123 (let ((u (- n 1))) (let ((v (count u))) v))))))) (count 8)) 123)
;
;(test 'x 'FAIL)
;(test '(let ((f (lambda () f))) (f)) 'FAIL)
