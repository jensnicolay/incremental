#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")

(provide conc-eval)

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
  ;(printf "ev ~v in ~v\n" e s)
  (match e
    ((«lit» _ d)
     ;(printf "-> ~v\n" ((lattice-α lat) d))
     ((lattice-α lat) d))
    ((«id» _ x)
     (let ((d (lookup-variable x s g lat parent)))
       ;(printf "-> ~v\n" d)
       d))
    ((«lam» _ _ _)
     ;(printf "-> clo ~v\n" e)
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
    ((«set!» _ _ _)
     ((lattice-α lat) 'undefined))
    ((«app» _ («id» _ x) e-rands) ;TODO: ((lam ...) rands)
     (let ((κ (state-κ s)))
       (let ((S-succ (successors s g)))
         ;(printf "successors ~v = ~v\n" s S-succ)
         (let loop ((W S-succ) (d (lattice-⊥ lat)) (prim (set-empty? S-succ)))
           (if (set-empty? W)
               (if prim
                   (let ((d-rands (map (lambda (e-rand) (ev e-rand s g lat parent)) e-rands))
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
                   ((state e-body (ctx (== e) _ _))
                    ;(printf "\t~v: compound app with body ~v\n" e e-body)
                    (loop (set-rest W) ((lattice-⊔ lat) d (ev e-body s* g lat parent)) prim))
                   (_
                    (loop (set-rest W) d #t)))))))))))

(define (lookup-static x s g lat parent)
  ;(printf "lookup-static ~v ~v\n" x s)

  (define (ast-helper e κ)
    (let ((pa (parent e)))
      ;(printf "ast-helper ~v e ~v pa ~v\n" x e pa)
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
        ((«set!» _ _ (== e))
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
    ;(printf "find-lambda ~v ~v\n" e-lam s)
    (let loop ((W (predecessors s g)) (S S) (res (set)))
      (if (set-empty? W)
          res
          (let ((s (set-first W)))
            ;(printf "lam ~v\n" s)
            (match s
              ((state (== e-lam) κ)
               ;(printf "found lam ~v => ~v\n" e-lam s)
               (loop (set-rest W) (set-add S s) (set-union res (ast-helper e-lam κ))))
              (_ (loop (set-union (set-rest W) (predecessors s g)) (set-add S s) res)))))))
  
  (let ((res (ast-helper (state-e s) (state-κ s))))
    ;(printf "looked up static ~v = ~v\n" x res)
    res))

(define (lookup-dynamic β s g lat parent)
  ;(printf "lookup-dynamic ~v ~v\n" β s)

  (match-let (((binding e-β κ-β) β))
    (let loop ((W (set s)) (S (set)) (d (lattice-⊥ lat)))
      (if (set-empty? W)
          d
          (let ((s (set-first W)))
            (if (set-member? S s)
                (loop (set-rest W) S d)
                (let ((prs (predecessors s g)))
                  (if (set-empty? prs)
                      (let ((prim-cons (assoc («id»-x e-β) (lattice-global lat))))
                        (match prim-cons
                          ((cons _ d-prim)
                           (loop (set-rest W) (set-add S s) ((lattice-⊔ lat) d d-prim)))
                          (#f
                           (error "unbound variable" («id»-x e-β)))))
                      (let prs-loop ((prs prs) (W (set-rest W)) (d d))
                        (if (set-empty? prs)
                            (loop W (set-add S s) d)
                            (let ((s-pr (set-first prs)))
                              (match s-pr
                                ((state e κ)
                                 ;(printf "dyn ~v\n" s-pr)
                                 (match e
                                   ((«lit» _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«lam» _ _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«let» _ (== e-β) e-init _)
                                    (if (equal? κ κ-β)
                                        (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-init s g lat parent)))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ((«let» _ _ _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«letrec» _ (== e-β) e-init _)
                                    (if (equal? κ κ-β)
                                        (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev e-init s g lat parent)))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ((«letrec» _ _ _ _)
                                    (prs-loop (set-rest prs) (set-add W s-pr) d))
                                   ((«set!» _ («id» _ (== («id»-x e-β))) e-init)
                                    (let ((B (lookup-static («id»-x e-β) s-pr g lat parent)))
                                      ;(printf "β ~v\nB ~v\n" β B)
                                      (let binding-loop ((B B) (W W) (d d))
                                        (if (set-empty? B)
                                            (prs-loop (set-rest prs) W d)
                                            (let ((β* (set-first B)))
                                              (if (equal? β β*)
                                                  (binding-loop (set-rest B) W ((lattice-⊔ lat) d (ev e-init s-pr g lat parent)))
                                                  (binding-loop (set-rest B) (set-add W s-pr) d)))))))
                                   ((«set!» _ _ _)
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
                                                (if (equal? (car xs) e-β)
                                                    (prs-loop (set-rest prs) W ((lattice-⊔ lat) d (ev (car e-args) s-pr g lat parent)))
                                                    (param-loop (cdr xs) (cdr e-args))))))
                                        (prs-loop (set-rest prs) (set-add W s-pr) d)))
                                   ))
                                ))))))))))))
    
  
(define (lookup-variable x s g lat parent)
  ;(printf "lookup-variable ~v ~v\n" x s)
  (let loop ((W (lookup-static x s g lat parent)) (d (lattice-⊥ lat)))
    (if (set-empty? W)
        d
        (loop (set-rest W) ((lattice-⊔ lat) d (lookup-dynamic (set-first W) s g lat parent))))))

(define (explore e lat)

  (define parent (make-parent e))
  
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
                 ;(printf "popping ~v\n" s)
                 (if (set-member? S s)
                     (graph-bw (set-rest W) S κs)
                     (match s
                       ((state (== e-app) κ*)
                        (graph-bw (set-rest W) (set-add S s) (set-add κs (state-κ s))))
                       (_
                        (graph-bw (set-union (set-rest W) (hash-ref bwd s (set))) (set-add S s) κs)))))))))))
               
      
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
         (let ((κs (stack-pop (state e κ))))
           ;(printf "pop e ~v κ ~v = ~v\n" e κ κs)
           (for/fold ((S-succ (set))) ((κ* (in-set κs)))
             (set-union S-succ (cont (ctx-e κ) κ*)))))
        (#f (set)))))
  
  (define (step s)
    ;(printf "\n#~v\nstep ~v\n" (state->statei s) s)

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
                (d-new (ev e-init s g lat parent)))
           (unless (⊑ d-new d-current)
             (set! Δi (add1 Δi)))
           (cont e κ))) ; only atomic update exps!
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
                   ((prim2 _ _)
                    (loop (set-rest W) (set-union S-succ (cont e κ)))))))))))

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
    
  (let ((s0 (state e (ctx #f #f (count!)))))
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
      ((lattice-⊔ lat) d (ev (state-e s) s g lat parent)))))

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
; (compile '(let ((f (lambda () (let ((x 3)) x))))
;             (let ((y (f)))
;               y))))


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