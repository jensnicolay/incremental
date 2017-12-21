#lang racket

(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")

(provide (struct-out semantics))
(provide (struct-out ctx)) ; mmm... should be opaque to semantics
(provide create-scheme-semantics)

;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)
(struct clo (lam ρ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<clo ~a>" («lam»-l (clo-lam v)))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))
(struct addr (a) #:transparent)

(struct ctx (e clo rands A) #:transparent)

(struct semantics (inject evaluate continue))

(define (create-scheme-semantics lattice alloc kalloc conc-alloc strong-updates)

  (define α (lattice-α lattice))
  (define γ (lattice-γ lattice))
  (define ⊥ (lattice-⊥ lattice))
  (define ⊑ (lattice-⊑ lattice))
  (define ⊔ (lattice-⊔ lattice))
  (define true? (lattice-true? lattice))
  (define false? (lattice-false? lattice))
  (define α-eq? (lattice-eq? lattice))

  (define (env-lookup ρ x)
    (hash-ref ρ x))
  
  (define (env-addresses ρ)
    (list->set (hash-values ρ)))
  
  (define (env-bind ρ x a)
    (hash-set ρ x a))
  
  (define (store-lookup σ a)
    (hash-ref σ a))
    
  (define (store-alloc σ a d)
    (if (hash-has-key? σ a) 
        (let* ((current (hash-ref σ a))
               (updated (⊔ current d)))
          (if (equal? current updated)
              σ
              (hash-set σ a updated)))
        (hash-set σ a d)))
  
  (define (store-update σ a d)
    (let* ((current (hash-ref σ a))
           (updated (if strong-updates
                        d
                        (⊔ current d))))
      (if (equal? current updated)
          σ
          (hash-set σ a updated))))

  (define (stack-lookup Ξ τ)
    (hash-ref Ξ τ))
  
  (define (stack-alloc κ stack Ξ)
    (let ((stacks (hash-ref Ξ κ #f)))
      (if stacks
          (if (set-member? stacks stack)
            Ξ
            (hash-set Ξ κ (set-add stacks stack)))
          (hash-set Ξ κ (set stack)))))

  (define (stack-pop ι κ Ξ G)
  (if (null? ι)
      (if κ
          (if (set-member? G κ)
              (set)
              (let ((ικs (stack-lookup Ξ κ)))
                (for/fold ((R (set))) ((ικ ικs))
                  (set-union R (stack-pop (car ικ) (cdr ικ) Ξ (set-add G κ))))))
          (set (list '() #f G)))
      (set (list ι κ G))))

  (define (stack-addresses ι κ σ γ)
    (let ((A (for/fold ((A (set))) ((φ ι))
               (set-union A (touches φ)))))
      (set-union (if κ (ctx-A κ) (set)) (reachable A σ γ))))

  (define (touches d)
    (if (set? d)
        (for/fold ((as (set))) ((v d)) (set-union as (touches v)))
        (match d
          ((clo _ ρ) (env-addresses ρ))
          ((letk _ _ ρ) (env-addresses ρ))
          ((letreck _ _ ρ) (env-addresses ρ))
          ((addr a) (set a))
          ((cons x y) (set-union (touches x) (touches y)))
          (_ (set)))))

  (define (reachable A σ γ)
    (let loop ((A A) (R (set)))
      (if (set-empty? A)
          R
          (let ((a (set-first A)))
            (if (set-member? R a)
                (loop (set-rest A) R)
                (let* ((v (γ (store-lookup σ a)))
                       (T (touches v)))
                  (loop (set-union (set-rest A) T) (set-add R a))))))))
  
  ;(define (gc s Ξ γ ctx-A)
  ;  (match s
  ;    ((ev e ρ σ ι κ)
  ;     (let* ((ρ* (↓ ρ (free e)))
  ;           (R (reachable (set-union (env-addresses ρ*) (stack-addresses ι κ ctx-A)) σ γ))
  ;            (σ* (↓ σ R)))
  ;       (ev e ρ* σ* ι κ)))
  ;    ((ko ι κ v σ)
  ;     (let* ((R (reachable (set-union (touches v) (stack-addresses ι κ ctx-A)) σ γ))
  ;            (σ* (↓ σ R)))
  ;       (ko ι κ v σ*)))))
  
  (define (alloc-literal e σ)
    (define (alloc-helper e)
      (if (pair? e)
          (let ((car-v (alloc-helper (car e))))
            (let ((cdr-v (alloc-helper (cdr e))))
              (let ((a (alloc e e)))
                (set! σ (store-alloc σ a (α (cons car-v cdr-v))))
                (α (addr a)))))
          (α e)))
    (values (alloc-helper e) σ))
  
  (define (eval-atom ae ρ σ)
    (match ae
      ((«lit» _ v)
       (α v))
      ((«id» _ x)
       (let ((a (env-lookup ρ x)))
         (store-lookup σ a)))
      ((«lam» _ x e)
       (let ((cl (clo ae ρ)))
         (α cl)))
      ((«quo» _ atom)
       (α atom))
      (_ (error "cannot handle ae" ae))))
  
  (define (apply-local-kont σ ι κ v Ξ evaluate continue)
    (match ι
      ((cons (letk x e ρ) ι)
       (let* ((a (alloc x κ))
              (ρ* (env-bind ρ («id»-x x) a))
              (σ* (store-alloc σ a v)))
         (evaluate e ρ* σ* ι κ Ξ)))
      ((cons (letreck x e ρ) ι)
       (let* ((a (env-lookup ρ («id»-x x)))
              (σ* (store-update σ a v)))
         (evaluate e ρ σ* ι κ Ξ)))
      (_ (continue v σ ι κ Ξ))))
  
  (define (apply-proc e d-clo rands σ-caller ι κ Ξ evaluate)
    (match-let (((clo («lam» _ x e0) ρ) d-clo))
      (define (bind-loop x vs ρ σ)
        (match x
          ('()
           (let* ((A (stack-addresses ι κ σ γ))
                  (κ* (kalloc e clo rands A))
                  (Ξ* (stack-alloc κ* (cons ι κ) Ξ)))
             (evaluate e0 ρ σ '() κ* Ξ*)))
          ((cons x xs)
           (if (null? vs)
               (set)
               (let* ((a (alloc x e))
                      (ρ* (env-bind ρ («id»-x x) a))
                      (σ* (store-alloc σ a (car vs))))
                 (bind-loop xs (cdr vs) ρ* σ*))))))
      (bind-loop x rands ρ σ-caller)))
  
  (define (evaluate0 e ρ σ ι κ Ξ evaluate continue)
    (match e
      ((? ae? ae)
       (let ((d (eval-atom ae ρ σ)))
         (continue d σ ι κ Ξ)))
      ((«if» _ ae e1 e2)
       (let ((d (eval-atom ae ρ σ)))
         (when (true? d)
           (evaluate e1 ρ σ ι κ Ξ))
         (when (false? d)
           (evaluate e2 ρ σ ι κ Ξ))))
      ((«let» _ x e0 e1)
       (evaluate e0 ρ σ (cons (letk x e1 ρ) ι) κ Ξ))
      ((«letrec» _ x e0 e1)
       (let* ((a (alloc x κ))
              (ρ* (env-bind ρ («id»-x x) a))
              (σ* (store-alloc σ a ⊥)))
         (evaluate e0 ρ* σ* (cons (letreck x e1 ρ*) ι) κ Ξ)))
      ((«set!» _ x ae)
       (let* ((d (eval-atom ae ρ σ))
              (a (env-lookup ρ («id»-x x)))
              (σ* (store-update σ a d)))
         (continue (α 'undefined) σ* ι κ Ξ)))
      ((«quo» _ e)
       (let-values (((v σ*) (alloc-literal e σ)))
         (continue v σ* ι κ Ξ)))
      ((and («app» _ rator rands) e)
       (let ((v (eval-atom rator ρ σ)))
         (let rands-loop ((rands rands) (rvs '()))
           (if (null? rands)
               (for ((w (γ v)))
                 (match w
                   ((clo _ _)
                    (apply-proc e w (reverse rvs) σ ι κ Ξ evaluate))
                   ((prim name proc)
                    (proc e (reverse rvs) σ ι κ Ξ continue))
                   ((prim2 _ proc)
                    (continue (apply proc (reverse rvs)) σ ι κ Ξ))))
               (let ((v (eval-atom (car rands) ρ σ)))
                 (rands-loop (cdr rands) (cons v rvs)))))))))
  
  (define (continue0 v σ ι κ Ξ evaluate continue)
    (unless (or (and (null? ι) (not κ)) (eq? v ⊥))
      (let ((ικGs (stack-pop ι κ Ξ (set))))
        (let loop ((ικGs ικGs))
          (unless (set-empty? ικGs)
            (let* ((ικG (set-first ικGs))
                   (ι (car ικG))
                   (κ (cadr ικG))
                   (G (caddr ικG)))
              (apply-local-kont σ ι κ v Ξ evaluate continue)
              (loop (set-rest ικGs))))))))

  (define (inject0 e evaluate)

    (define (prim-car e rands σ ι κ Ξ continue)
      (match rands
        ((list v1)
         (let ((v (for/fold ((v ⊥)) ((w (γ v1)))
                    (match w
                      ((addr a)
                       (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                         (match ww
                           ((cons v-car _) (⊔ v v-car))
                           (_ v))))
                      (_ v))))) 
           (continue v σ ι κ Ξ)))))
    
    (define (prim-cdr e rands σ ι κ Ξ continue)
      (match rands
        ((list v1)
         (let ((v (for/fold ((v ⊥)) ((w (γ v1)))
                    (match w
                      ((addr a)
                       (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                         (match ww
                           ((cons _ v-cdr) (⊔ v v-cdr))
                           (_ v))))
                      (_ v))))) 
           (continue v σ ι κ Ξ)))))

    (define (prim-set-car! e rands σ ι κ Ξ continue)
      (match rands
        ((list v1 v2)
         (let ((σ* (for/fold ((σ σ)) ((w (γ v1)))
                     (match w
                       ((addr a)
                        (for/fold ((σ σ)) ((ww (γ (store-lookup σ a))))
                          (match ww
                            ((cons _ v-cdr)
                             (store-update σ a (α (cons v2 v-cdr))))
                            (_ σ))))
                       (_ σ)))))
           (continue (α 'undefined) σ* ι κ Ξ)))))
    
    (define (prim-set-cdr! e rands σ ι κ Ξ continue)
      (match rands
        ((list v1 v2)
         (let ((σ* (for/fold ((σ σ)) ((w (γ v1)))
                     (match w
                       ((addr a)
                        (for/fold ((σ σ)) ((ww (γ (store-lookup σ a))))
                          (match ww
                            ((cons v-car _)
                             (store-update σ a (α (cons v-car v2))))
                            (_ σ))))
                       (_ σ)))))
           (continue (α 'undefined) σ* ι κ Ξ)))))
    
    (define (prim-cons e rands σ ι κ Ξ continue)
      (match rands
        ((list v1 v2)
         (let* ((a (alloc e κ))
                (v (α (cons v1 v2)))
                (σ* (store-alloc σ a v)))
           (continue (α (addr a)) σ* ι κ Ξ)))))
    
    (define (prim-pair? e rands σ ι κ Ξ continue)
      (match rands
        ((list v1)
         (let ((v (for/fold ((v ⊥)) ((w (γ v1)))
                    (match w
                      ((addr a)
                       (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                         (⊔ v (α (pair? ww)))))
                      (_ (α #f))))))
           (continue v σ ι κ Ξ)))))
    
    (define (prim-to-string e rands σ ι κ Ξ continue)
      (define (helper v seen)
        (match v
          ((addr a)
           (if (set-member? seen a)
               (continue (α (~a v)) σ ι κ Ξ)
               (set-for-each (γ (store-lookup σ a)) (lambda (w) (helper w (set-add seen a))))))
          ((cons v1 v2)
           (let ((s1 (helper v1 seen))
                 (s2 (helper v2 seen)))
             (for ((sσ1 s1) (sσ2 s2))
               (continue (α (~a (cons (car sσ1) (car sσ2)))) σ ι κ Ξ))))
          (_ (continue (α (~a v)) σ ι κ Ξ))))
      (match rands
        ((list d)
         (set-for-each (γ d) (lambda (w) (helper w (set)))))))
    
    (define (eq?-helper v1 v2)
      (match* (v1 v2)
        (((addr a1) (addr a2))
         (α (equal? a1 a2)))
        ((_ _) (α-eq? v1 v2))))
    
    (define (prim-eq? e rands σ ι κ Ξ continue)
      (match rands
        ((list w1 w2)
         (let ((v (for*/fold ((v ⊥)) ((v1 w1) (v2 w2)) (⊔ v (eq?-helper v1 v2)))))
           (continue v σ ι κ Ξ)))))
    
    (define (prim-error e rands σ ι κ Ξ continue)
      'do-nothing)
    
    (let ((global* (append (lattice-global lattice)
                           `(("eq?"               . ,(α (prim "eq?" prim-eq?)))
                             ("cons"              . ,(α (prim "cons" prim-cons)))
                             ("car"               . ,(α (prim "car" prim-car)))
                             ("cdr"               . ,(α (prim "cdr" prim-cdr)))
                             ("set-car!"          . ,(α (prim "set-car!" prim-set-car!)))
                             ("set-cdr!"          . ,(α (prim "set-cdr!" prim-set-cdr!)))
                             ("pair?"             . ,(α (prim "pair?" prim-pair?)))
                             ("~a"                . ,(α (prim "~a" prim-to-string)))
                             ("list->string"      . ,(α (prim "list->string" prim-to-string)))
                             ("error"             . ,(α (prim "error" prim-error)))
                             ;("vector-length"    . ,(α (prim "vector-length" prim-vector-length)))
                             ;("vector-copy"      . ,(α (prim "vector-copy" prim-vector-copy)))
                             ))))
      (let loop ((global global*) (ρ (hash)) (σ (hash)))
        (match global
          ('()
           (let* ((compiled-e (compile e))
                  (ρ* (↓ ρ (free compiled-e)))
                  (R (reachable (env-addresses ρ*) σ γ))
                  (σ* (↓ σ R)))
             (evaluate compiled-e ρ* σ* '() #f (hash))))
          ((cons (cons x v) r)
           (let* ((a (conc-alloc))
                  (ρ* (env-bind ρ x a))
                  (σ* (store-alloc σ a v)))
             (loop r ρ* σ*)))))))

  (semantics inject0 evaluate0 continue0))