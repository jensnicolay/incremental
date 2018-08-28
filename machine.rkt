#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")

(provide conc-eval)

(define ns (make-base-namespace))

;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)
;(struct clo (e) #:transparent
 ; #:property prop:custom-write (lambda (v p w?)
  ;                               (fprintf p "<clo ~v>" (clo-e v))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))
(struct addr (a) #:transparent)
(struct binding (x e κ) #:transparent)
;(struct ctx (e d-proc n) #:transparent ; (e-app d-proc n)
; #:property prop:custom-write (lambda (v p w?)
;                                 (fprintf p "<ctx ~v ~v>" (ctx-e v) (ctx-n v))))

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

(define (body-expression? e parent)
  («lam»? (parent e)))


(define (ev e access s g lat parent) ; general TODO: every fw movement should be restrained to previous path(s)

  (printf "ev ~v ~v in ~v\n" e access s)
  (match e
    ((«lit» _ d)
     ;(printf "-> ~v\n" ((lattice-α lat) d))
     ((lattice-α lat) d))
    ((«id» _ x)
     (let ((d (lookup-variable x s g lat parent)))
       ;(printf "-> ~v\n" d)
       d))
    ((«lam» _ _ _)
     ;(printf "-> clo ~v\n" s)
     ((lattice-α lat) s))
    ((«let» _ _ _ e-body)
     (let graph-fw ((W (successors s g)) (S (set)) (d (lattice-⊥ lat)))
       (if (set-empty? W)
           d
           (let ((s* (set-first W)))
             (if (set-member? S s*)
                 (graph-fw (set-rest W) S d)
                 (match s*
                   ((state (== e-body) (== (state-κ s)))
                    (graph-fw (set-rest W) (set-add S s*) ((lattice-⊔ lat) d (ev e-body '() s* g lat parent))))
                   (_
                    (graph-fw (set-union W (successors s* g)) (set-add S s*) d))))))))
    ((«if» _ _ _ _)
     (let graph-succ ((W (successors s g)) (d (lattice-⊥ lat)))
       (if (set-empty? W)
           d
           (let ((s* (set-first W)))
             (graph-succ (set-rest W) ((lattice-⊔ lat) d (ev (state-e s*) '() s* g lat parent)))))))
    ((«set!» _ _ _)
     ((lattice-α lat) 'undefined))
    ((«app» _ («id» _ x) e-rands) ;TODO: ((lam ...) rands)
     (let ((κ (state-κ s)))
       (let ((S-succ (successors s g)))
         ;(printf "successors ~v = ~v\n" s S-succ)
         (let loop ((W S-succ) (d (lattice-⊥ lat)) (prim (set-empty? S-succ)))
           (if (set-empty? W)
               (if prim
                   (let ((d-rands (map (lambda (e-rand) (ev e-rand '() s g lat parent)) e-rands))
                         (proc (let ((prim-cons (assoc x (lattice-global lat))))
                                   (match prim-cons
                                     ((cons _ (prim2 _ proc))
                                      proc)))))
                     ;(printf "~v: primitive app ~v on ~v\n" e x d-rands)
                     (let ((d* (apply proc d-rands)))
                       ((lattice-⊔ lat) d d*)))
                   d)
               (let ((s* (set-first W)))
                 (match s*
                   ((state (? (lambda (e) (body-expression? e parent)) e-body) _)
                    ;(printf "\t~v: compound app with body ~v\n" e e-body)
                    (loop (set-rest W) ((lattice-⊔ lat) d (ev e-body '() s* g lat parent)) prim))
                   (_
                    (loop (set-rest W) d #t)))))))))
    ((«car» _ (and e-id («id» _ x)))
     (let ((d (lookup-path x (cons 'car access) s g lat parent)))
       (printf "-> ~v\n" d)
       d))
    ((«cdr» _ (and e-id («id» _ x)))
     (let ((d (lookup-path x (cons 'cdr access) s g lat parent)))
       (printf "-> ~v\n" d)
       d))
    ((«cons» _ ar dr)
         (match access
           ('() ((lattice-α lat) s))
           (`(car . ,access2) (ev ar access2 s g lat parent))
           (`(cdr . ,access2) (ev dr access2 s g lat parent))))
    ))

(define (graph-find g s dir e κ)
  (let graph-fw ((W (dir s g)) (S (set)) (res (set)))
    (if (set-empty? W)
        res
        (let ((s* (set-first W)))
          (if (set-member? S s*)
              (graph-fw (set-rest W) S res)
              (match s*
                ((state (== e) (== κ))
                 (graph-fw (set-rest W) (set-add S s*) (set-add res s*)))
                (_
                 (graph-fw (set-union W (dir s* g)) (set-add S s*) res))))))))

(define (graph-find-fw g s e κ)
  (graph-find g s successors e κ))

(define (graph-find-bw g s e κ)
  (graph-find g s predecessors e κ))

(define (lookup-static x s g lat parent)
  ;(printf "lookup-static ~v ~v\n" x s)

  (define (ast-helper W B)
    (if (set-empty? W)
        B
        (let* ((s (set-first W))
               (e (state-e s))
               (κ (state-κ s))
               (pa (parent e)))
      ;(printf "ast-helper ~v e ~v pa ~v\n" x e pa)
      (match pa
        ((«let» _ _ (== e) _)
         (ast-helper (set-union (set-rest W) (graph-find-bw g s pa κ)) B))
        ((«let» _ (and e-decl («id» _ (== x))) _ _)
         (ast-helper (set-rest W) (set-add B (binding x e-decl κ))))
        ((«let» _ _ _ _)
         (ast-helper (set-union (set-rest W) (graph-find-bw g s pa κ)) B))
        ((«letrec» _ (and e-decl («id» _ (== x))) _ _)
         (ast-helper (set-rest W) (set-add B (binding x e-decl κ))))
        ((«letrec» _ _ _ _)
         (ast-helper (set-union (set-rest W) (graph-find-bw g s pa κ)) B))
        ((«app» _ _ _)
         (ast-helper (set-union (set-rest W) (graph-find-bw g s pa κ)) B))
        ((«if» _ _ _ _)
         (ast-helper (set-union (set-rest W) (graph-find-bw g s pa κ)) B))
        ((«set!» _ _ (== e))
         (ast-helper (set-union (set-rest W) (graph-find-bw g s pa κ)) B))
        ((«lam» _ (list xs ...) _) ; s evals body exp
         (let param-loop ((xs xs))
           (if (null? xs)
               (ast-helper (set-union (set-rest W) (find-lambda s pa)) B)
               (let ((e-decl (car xs)))
                 (match e-decl
                   ((«id» _ (== x))
                    (ast-helper (set-rest W) (set-add B (binding x e-decl κ))))
                   (_
                    (param-loop (cdr xs))))))))
        (#f (ast-helper (set-rest W) (set-add B (binding x #f #f)))) ; no static decl found
        (_ (error "cannot handle expression" pa))))))

  (define (find-lambda s pa) ; s should eval body expr
    ;(printf "find-lambda ~v ~v\n" s pa)
    (let graph-pr ((W (predecessors s g)) (res (set)))
      (if (set-empty? W)
          res
          (let ((s-pr (set-first W)))
            ;(printf "compound app state ~v\n" s-pr)
            (match s-pr 
              ((state («app» _ e-rator _) _)
               (let ((d-rators (ev e-rator '() s-pr g lat parent)))
                 ;(printf "d-rators ~v\n" d-rators)
                 ((lattice-γ lat) d-rators))))))))

   
  (let ((res (ast-helper (set s) (set))))
    ;(printf "looked up static ~v = ~v\n" x res)
    res))

(define (lookup-dynamic b s g lat parent)
  (printf "lookup-dynamic ~v ~v\n" b s)
  (match-let (((binding x e-b κ-b) b))
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
                           (#f (error "unbound variable" x))))
                       (let prs-loop ((prs prs) (W (set-rest W)) (d d))
                         (if (set-empty? prs)
                             (loop W (set-add S s) d)
                             (let ((s-pr (set-first prs)))
                               (printf "dyn ~v\n" s-pr)
                               (match s-pr
                                 ((state e κ)
                                  (match e
                                    ((«lit» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«lam» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«let» _ (== e-b) e-init _)
                                     (if (equal? κ κ-b)
                                         (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-init '() s g lat parent)))
                                         (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                    ((«let» _ _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«letrec» _ (== e-b) e-init _)
                                     (if (equal? κ κ-b)
                                         (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-init '() s g lat parent)))
                                         (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                    ((«letrec» _ _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«set!» _ («id» _ (== x)) e-update)
                                     (let ((B (lookup-static x s-pr g lat parent)))
                                       ;(printf "β ~v\nB ~v\n" β B)
                                       (let binding-loop ((B B) (W W) (d d))
                                         (if (set-empty? B)
                                             (prs-loop (set-rest prs) W d)
                                             (let ((b* (set-first B)))
                                               (if (equal? b b*)
                                                   (binding-loop (set-rest B) W ((lattice-⊔ lat) d (ev e-update '() s-pr g lat parent)))
                                                   (binding-loop (set-rest B) (set-add W s-pr) d)))))))
                                    ((«set!» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«id» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«if» _ _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«app» _ _ _)
                                     (if (and (body-expression? (state-e s) parent) ; s-pr is compound call, s is proc entry
                                              (equal? (state-κ s) κ-b))
                                         (let* ((e-proc (parent (state-e s)))
                                                (xs («lam»-x e-proc)))
                                           (let param-loop ((xs xs) (e-args («app»-aes e)))
                                             (if (null? xs)
                                                 (prs-loop (set-rest prs) (set-add W s-pr) d)
                                                 (if (equal? (car xs) e-b)
                                                     (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev (car e-args) '() s-pr g lat parent)))
                                                     (param-loop (cdr xs) (cdr e-args))))))
                                         (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                    ((«set-car!» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«car» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«cdr» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ((«cons» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) d))
                                    ))
                                 ))))))))))))
  
(define (lookup-variable x s g lat parent)
  (printf "lookup-variable ~v ~v\n" x s)
  (let ((B (lookup-static x s g lat parent)))
    (let loop ((W B) (d (lattice-⊥ lat)))
      (if (set-empty? W)
          d
          (let ((b (set-first W)))
            (let ((d* (lookup-dynamic b s g lat parent)))
              (loop (set-rest W) ((lattice-⊔ lat) d d*))))))))

(define (lookup-path x access s g lat parent)
  (printf "lookup-path ~v ~v ~v\n" x access s)
  (let ((B (lookup-static x s g lat parent)))
    (let loop ((W B) (d (lattice-⊥ lat)))
      (if (set-empty? W)
          d
          (let ((b (set-first W)))
            (let ((E (lookup-root-expression b access s g lat parent)))
              (printf "roots of ~v ~v are ~v\n" b access E)
              (let root-loop ((W-E E) (d d))
                (if (set-empty? W-E)
                    (loop (set-rest W) d)
                    (let ((b-root (set-first W-E)))
                      (let ((d* (lookup-dynamic2 b-root s g lat parent)))
                        (printf "root ~v value ~v\n" b-root d*)
                        (root-loop (set-rest W-E) ((lattice-⊔ lat) d d*))))))))))))

(define (dobido e access s g lat parent)
  (printf "dobido ~v ~v ~v\n" e access s)
  (match e
    ((«cons» _ e-car e-cdr)
     (match access
       ((cons 'car access*)
        (if («id»? e-car)
            (lookup-root-expression-B («id»-x e-car) access* s g lat parent)
            (set (cons e-car (state-κ s)))))
       ((cons 'cdr access*)
        (if («id»? e-cdr)
            (lookup-root-expression-B («id»-x e-cdr) access* s g lat parent)
            (set (cons e-cdr (state-κ s)))))
       ))
    ((«car» _ («id» _ x-car))
     (lookup-root-expression-B x-car (cons 'car access) s g lat parent))
    ((«cdr» _ («id» _ x-cdr))
     (lookup-root-expression-B x-cdr (cons 'cdr access) s g lat parent))
    ((«id» _ x)
     (lookup-root-expression-B x access s g lat parent))
    ;((«app» _ e-rator e-rands)
    ; (let ((S-succ (successors s g)))
    ;   (let succ-loop ((S-succ S-succ) (E (set)))
    ;     (if (set-empty? succ-loop)
             
    ))

(define (lookup-root-expression-B x access s g lat parent)
  (let ((B (lookup-static x s g lat parent)))
    (let loop ((W B) (E (set)))
      (if (set-empty? W)
          E
          (let ((b (set-first W)))
            (let ((E* (lookup-root-expression b access s g lat parent)))
              (loop (set-rest W) (set-union E E*))))))))

(define (lookup-root-expression b access s g lat parent)
  (printf "lookup-root-expression ~v ~v\n" b s)
  (match-let (((binding x e-b κ-b) b))
    (let loop ((W (set s)) (S (set)) (E (set)))
      (if (set-empty? W)
           E
           (let ((s (set-first W)))
             (if (set-member? S s)
                 (loop (set-rest W) S E)
                 (let ((prs (predecessors s g)))
                   (if (set-empty? prs)
                       (loop (set-rest W) (set-add S s) (set-add E #f))
                       (let prs-loop ((prs prs) (W (set-rest W)) (E E))
                         (if (set-empty? prs)
                             (loop W (set-add S s) E)
                             (let ((s-pr (set-first prs)))
                               (printf "re ~v ~v\n" s-pr access)
                               (match s-pr
                                 ((state e κ)
                                  (match e
                                    ((«lit» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«lam» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«let» _ (== e-b) e-init _)
                                     (if (equal? κ κ-b)
                                         (let ((E* (dobido e-init access s-pr g lat parent)))
                                           (prs-loop (set-rest prs) W (set-union E E*)))
                                         (prs-loop (set-rest prs) (set-add W s-pr) E)))
                                    ((«let» _ _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«set!» _ («id» _ x) e-update)
                                     (let ((B (lookup-static x s-pr g lat parent)))
                                       (let binding-loop ((B B) (W W) (E E))
                                         (if (set-empty? B)
                                             (prs-loop (set-rest prs) W E)
                                             (let ((b* (set-first B)))
                                               (if (equal? b b*)
                                                   (let ((E* (dobido e-update access s-pr g lat parent)))
                                                     (binding-loop (set-rest B) W (set-union E E*)))
                                                   (binding-loop (set-rest B) (set-add W s-pr) E)))))))
                                    ((«set!» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«id» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«if» _ _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«app» _ _ _)
                                     (if (and (body-expression? (state-e s) parent) ; s-pr is compound call, s is proc entry
                                              (equal? (state-κ s) κ-b))
                                         (let* ((e-proc (parent (state-e s)))
                                                (xs («lam»-x e-proc)))
                                           (let param-loop ((xs xs) (e-args («app»-aes e)))
                                             (if (null? xs)
                                                 (prs-loop (set-rest prs) (set-add W (cons s-pr access)) E)
                                                 (if (equal? (car xs) e-b)
                                                     (let ((E* (dobido (car e-args) access s-pr g lat parent)))
                                                       (prs-loop (set-rest prs) W (set-union E E*)))
                                                     (param-loop (cdr xs) (cdr e-args))))))
                                         (prs-loop (set-rest prs) (set-add W s-pr) E)))
                                    ((«set-car!» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«set-cdr!» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«car» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«cdr» _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ((«cons» _ _ _)
                                     (prs-loop (set-rest prs) (set-add W s-pr) E))
                                    ))
                                 ))))))))))))


(define (lookup-dynamic2 b-root s g lat parent)
  (printf "lookup-dynamic2 ~v ~v\n" b-root s)
  (match-let (((cons e-b κ-b) b-root))
  (let loop ((W (set s)) (S (set)) (d (lattice-⊥ lat)))
    (if (set-empty? W)
        d
        (let ((s (set-first W)))
          (if (set-member? S s)
              (loop (set-rest W) S d)
              (let ((prs (predecessors s g)))
                (if (set-empty? prs)
                    (error "unbound root" b-root)
                    (let prs-loop ((prs prs) (W (set-rest W)) (d d))
                      (if (set-empty? prs)
                          (loop W (set-add S s) d)
                          (let ((s-pr (set-first prs)))
                            (printf "dyn2 ~v for b-root ~v\n" s-pr b-root)
                            (match s-pr
                              ((state e κ)
                               (match e
                                 ((«lit» _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«lam» _ _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«let» _ _ _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«letrec» _ _ _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«set!» _ _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«id» _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«if» _ _ _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«app» _ _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«set-car!» _ («id» _ x) e-update)
                                  (let ((B (lookup-static x s g lat parent)))
                                    (let binding-loop ((B B) (W W) (d d))
                                      (if (set-empty? B)
                                          (prs-loop (set-rest prs) W d)
                                          (let ((b (set-first B)))
                                            (let ((E (lookup-root-expression b '(car) s-pr g lat parent)))
                                              (let ((alias? (set-member? E b-root)))
                                                (printf "binding ~v ~v roots ~v alias? ~v ? ~v\n" b '(car) E b-root alias?)
                                                (if alias?
                                                    (binding-loop (set-rest B) W ((lattice-⊔ lat) d (ev e-update '() s-pr g lat parent)))
                                                    (binding-loop (set-rest B) (set-add W s-pr) d)))))))))
                                 ((«set-cdr!» _ («id» _ x) e-update)
                                  (let ((B (lookup-static x s g lat parent)))
                                    (let binding-loop ((B B) (W W) (d d))
                                      (if (set-empty? B)
                                          (prs-loop (set-rest prs) W d)
                                          (let ((b (set-first B)))
                                            (let ((E (lookup-root-expression b '(cdr) s-pr g lat parent)))
                                              (let ((alias? (set-member? E b-root)))
                                                (printf "binding ~v ~v roots ~v alias? ~v ? ~v\n" b '(cdr) E b-root alias?)
                                                (if alias?
                                                    (binding-loop (set-rest B) W ((lattice-⊔ lat) d (ev e-update '() s-pr g lat parent)))
                                                    (binding-loop (set-rest B) (set-add W s-pr) d)))))))))
                                 ((«car» _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«cdr» _ _)
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ((«cons» _  (== e-b) _)
                                  (if (equal? κ κ-b)
                                      (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-b '() s-pr g lat parent)))
                                      (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                 ((«cons» _  _ (== e-b))
                                  (if (equal? κ κ-b)
                                      (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-b '() s-pr g lat parent)))
                                      (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                 ((«cons» _ _ _) ; TIODO not all cases handled!
                                  (prs-loop (set-rest prs) (set-add W s-pr) d))
                                 ))
                              ))))))))))))
    

(define (explore e lat)

  (define parent (make-parent e))
  
  ; state -> (set state...)
  (define fwd (hash))
  (define bwd (hash))
  
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
     
  (define (stack-pop s κ)
    (let graph-bw ((W (set s)) (S (set)) (S-app (set)))
      (if (set-empty? W)
          S-app
          (let ((s (set-first W)))
            ;(printf "popping ~a\n" s) 
            (if (set-member? S s)
                (graph-bw (set-rest W) S S-app)
                (match s
                  ((state (? (lambda (e) (body-expression? e parent))) (== κ))
                   (graph-bw (set-rest W) (set-add S s) (set-union S-app (hash-ref bwd s))))
                  (_
                   (graph-bw (set-union (set-rest W) (hash-ref bwd s (set))) (set-add S s) S-app))))))))
               
      
  (define (cont e κ)
    ;(printf "cont e ~v κ ~v\n" e κ)
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
        ((«set!» _ _ (== e))
         (cont p κ))
        ((«if» _ _ (== e) _)
         (cont p κ))
        ((«if» _ _ _ (== e))
         (cont p κ))
        ((«lam» _ _ (== e))
         (let ((S-app (stack-pop (state e κ) κ)))
           ;(printf "pop e ~v κ ~v = ~v\n" e κ κs)
           (for/fold ((S-succ (set))) ((s-app (in-set S-app)))
             (set-union S-succ (cont (state-e s-app) (state-κ s-app))))))
        (#f (set)))))
  
  (define (step s)
    (printf "\n#~v\nstep ~v\n" (state->statei s) s)

    (define (helper e κ)
      (match e
        ((? ae? e)
         (cont e κ))
        ((«let» _ _ init _)
         (set (state init κ)))
        ((«letrec» _ _ init _)
         (set (state init κ)))
        ((«set!» _ («id» _ x) e-init) ; expensive with the Δi :(
         (let* ((g (graph fwd bwd #f))
                (d-current (lookup-variable x s g lat parent)) 
                (d-new (ev e-init '() s g lat parent)))
           (unless (⊑ d-new d-current)
             (set! Δi (add1 Δi)))
           (cont e κ))) ; only atomic update exps!
        ((«if» _ e-cond e-then e-else)
         (let* ((g (graph fwd bwd #f))
                (d-cond (ev e-cond '() s g lat parent)))
           (set (state (if (true? d-cond) e-then e-else) κ))))
        ((«app» _ e-rator e-rands)
         (let* ((g (graph fwd bwd #f))
                (d-proc (ev e-rator '() s g lat parent)))
           (let loop ((W (γ d-proc)) (S-succ (set)))
             (if (set-empty? W)
                 S-succ
                 (match (set-first W)
                   ((state («lam» _ _ e-body) _)
                    (let* ((κ* (count!)) ; TODO ctxs hardcoded as concrete
                           (s* (state e-body κ*)))
                      (when (state-exists? s* g)
                        (set! Δi (add1 Δi)))
                      (loop (set-rest W) (set-add S-succ s*))))
                   ((state («set!» _ _ («lam» _ _ e-body)) _)
                    (let* ((κ* (count!)) ; CLONE (caused by atomic-only set!)
                           (s* (state e-body κ*)))
                      (when (state-exists? s* g)
                        (set! Δi (add1 Δi)))
                      (loop (set-rest W) (set-add S-succ s*))))
                   ((prim2 _ _)
                    (loop (set-rest W) (set-union S-succ (cont e κ)))))))))
        ((«cons» _ _ _)
         (cont e κ))
        ((«car» _ _)
         (cont e κ))
        ((«cdr» _ _)
         (cont e κ))
        ((«set-car!» _ _ _) ; Δi?
         (cont e κ))
        ((«set-cdr!» _ _ _) ; Δi?
         (cont e κ))
        ))

    (match s
      ((state e κ) (helper e κ))))

  (define (explore! W S)
    (unless (set-empty? W)
      (let ((s (set-first W)))
        (if (set-member? S s)
            (explore! (set-rest W) S)
            (let ((S* (set-add S s)))
              (let* ((Δi0 Δi)
                     (succs (step s))
                     (W* (set-union (set-rest W) succs))
                     (S* (if (> Δi Δi0)
                             (set)
                             (set-add S s))))
                ;(printf "TRANS ~v -> ~v\n" (state->statei s) (set-map succs state->statei))
                (add-transitions! s succs)
                (explore! W* S*)))))))

;  (define (incremental-update ast-update)
;    (match ast-update
;      ((replace e e*) (incremental-replace sys e e*))))
        
;  (define (incremental-replace sys e e*)
;  
;    (let ((S-rem (states-for-expression e g)))
;      (for ((s-rem (in-set S-rem)))
;        (let ((s* (state e* (state-κ s-rem))))
;          (replace-state! s-rem s*)
;          (let ((S-seen (list->set (hash-keys bwd))))
;            (explore! (set s*) S-seen)
;            (let ((S-value (value-flow s* g)))
;              (let value-loop ((S-value S-value))
;                (if (set-empty? S-value)
;                    (let ((S-ref (references s* g)))
;                      (let ref-loop ((S-ref S-ref))
;                        (if (set-empty? S-ref)
;                            'nothing
;                            
          
;    (define (value-flow e)
;      (match (parent e)
;        ((«let» _ x (== e) _) x)))
;  

;    (let value-loop ((e e) (control-refs '()))
;      (let ((decl (value-flow e parent)))
;        (let ((refs (find-ast-references («id»-x decl) (parent decl))))
;          (let ref-loop ((refs refs) (control-refs2 '()))
;            (if (null? refs)
;                (value-loop 
;                (let ((ref (car refs)))
;                  (if (in-operator-position? ref parent)
                    
                  

                        ;
    
  (let ((s0 (state e (count!))))
    (explore! (set s0) (set))
    (system (graph fwd bwd s0) parent))) ;incremental-update)))

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
      ((lattice-⊔ lat) d (ev (state-e s) '() s g lat parent)))))

(define (conc-eval e)
  (evaluate e conc-lattice))


;; incremental

(struct replace (exp new-exp) #:transparent)

; ast level
(define (perform-ast-replace ast e e*)
  (define (helper e**)
    (if (equal? e** e)
        e*
        (match e**
          ((«id» _ _) e**)
          ((«lit» _ _) e**)
          ((«quo» _ _) e**)
          ((«lam» l x e) («lam» l (helper x) (helper e)))
          ((«let» l x e0 e1) («let» l (helper x) (helper e0) (helper e1)))
          ((«letrec» l x e0 e1) («letrec» l (helper x) (helper e0) (helper e1)))
          ((«if» l ae e1 e2) («if» l (helper ae) (helper e1) (helper e2)))
          ((«set!» l x ae) («set!» l (helper x) (helper ae)))
          ((«app» l rator rands) («app» l (helper rator) (map helper rands)))
          (_ (error "cannot handle expression" e**)))))
  (helper ast))
                                                  
(define (perform-ast-update ast update)
  (match update
    ((replace e e*) (perform-ast-replace ast e e*))))

(define (find-ast-references x ast parent)
  (define (ast-helper e)
    (match e
      ((«id» _ (== x))
       (set e))
      ((«id» _ _)
       (set))
      ((«lit» _ _)
       (set))
      ((«quo» _ _)
       (set))
      ((«lam» _ x e)
       (let param-loop ((xs x))
         (if (null? xs)
             (ast-helper e)
             (match (car xs)
               ((«id» _ (== x)) (set))
               (_ (param-loop (cdr xs)))))))
      ((«let» _ («id» _ (== x)) e-init _)
       (ast-helper e-init))
      ((«let» _ _ e-init e-body)
       (set-union (ast-helper e-init) (ast-helper e-body)))
      ((«letrec» _ («id» _ (== x)) _ _)
       (set))
      ((«letrec» _ _ e-init e-body)
       (set-union (ast-helper e-init) (ast-helper e-body)))
      ((«if» _ ae e1 e2) (set-union (ast-helper ae) (ast-helper e1) (ast-helper e2)))
      ((«set!» _ _ ae) (ast-helper ae))
      ((«app» _ rator rands) (apply set-union (map ast-helper (cons rator rands))))
      (_ (error "cannot handle expression" e))))
  (ast-helper ast))
      
 
; system level
              

      
    

;;; TESTS

;(define (test-incremental e ast-update)
;  (let* ((ast (compile e))
;         (sys (explore ast conc-lattice))
;         (parent (system-parent sys))
;         (update (ast-update ast))
;         (ast* (perform-ast-update ast update))
;         (sys* (explore ast* conc-lattice))
;         (parent* (system-parent sys*)))
;    (incremental-update sys ast-update)))
 

;(test-incremental '(let ((x 1))
;                     (let ((y (+ x 1)))
;                       (let ((c (= y 2)))
;                         (let ((z (if c (set! x 2) (set! x 3))))
;                           (+ x y)))))
;                  (lambda (ast)
;                    (match-let (((«let» _ _ lit _) ast))
;                      (replace lit (compile '2)))))



;(conc-eval
; (compile '(letrec ((f (lambda (x) (let ((v (= x 2))) (if v x (let ((u (+ x 1))) (f u))))))) (f 0))))


;(conc-eval
; (compile
;  '(let ((o (cons 1 2))) (let ((f (lambda () o))) (let ((u (set-car! o 3))) (let ((w (f))) (car w)))))
;  ))
           


;(conc-eval
; (compile '(let ((x 1))
;             (let ((y (+ x 1)))
;               (let ((c (= y 2)))
;                 (let ((z (if c (set! x 2) (set! x 3))))
;                   (+ x y)))))))



;;; INTERESTING CASE is when the update exp of a set! can be non-atomic: first encountered set! when walking back is not the right one!
;;;; THEREFORE: we only allow aes as update exps
;;;(test '(let ((x 123)) (let ((y (set! x (set! x 456)))) x)) 'undefined)
;;;(test '(let ((x 123)) (let ((y (set! x (let ((u (set! x 456))) 789)))) x)) 789)

;;; SCHEME ERROR when setting before init
;;; (test '(letrec ((x (let ((u (set! x 123))) 456))) x) 456)