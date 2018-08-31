#lang racket

(require "general.rkt")
(require "ast.rkt")

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

;;;

(define (successor s g)
  (hash-ref (graph-fwd g) s #f))

(define (predecessor s g)
  (hash-ref (graph-bwd g) s #f))

(define (state-exists? s g)
  (hash-ref (graph-fwd g) s #f))

(define (body-expression? e parent)
  («lam»? (parent e)))

(define (ev e access s g parent) ; general TODO: every fw movement should be restrained to previous path(s)
  (printf "ev ~v ~v in ~v\n" e access s)
  (match e
    ((«lit» _ d)
     ;(printf "-> ~v\n" ((lattice-α lat) d))
     d)
    ((«id» _ x)
     (let ((d (lookup-variable x s g parent)))
       ;(printf "-> ~v\n" d)
       d))
    ((«lam» _ _ _)
     ;(printf "-> clo ~v\n" s)
     s)
    ((«let» _ _ _ e-body)
     (let graph-fw ((s* (successor s g)))
       (match s*
         ((state (== e-body) (== (state-κ s)))
          (ev e-body '() s* g parent))
         (_
          (graph-fw (successor s* g))))))
    ((«if» _ _ _ _)
     (let ((s* (successor s g)))
       (ev (state-e s*) '() s* g parent)))
    ((«set!» _ _ _)
     '<undefined>)
    ((«app» _ («id» _ x) e-rands) ;TODO: ((lam ...) rands)
     (let ((κ (state-κ s)))
       (let ((s* (successor s g)))
         (match s*
           (#f
            (let ((d-rands (map (lambda (e-rand) (ev e-rand '() s g parent)) e-rands))
                  (proc (eval (string->symbol x) ns)))
              ;(printf "~v: primitive app ~v on ~v\n" e x d-rands)
              (apply proc d-rands)))
           ((state (? (lambda (e) (body-expression? e parent)) e-body) _)
            ;(printf "\t~v: compound app with body ~v\n" e e-body)
            (ev e-body '() s* g parent))
           (_
            (let ((d-rands (map (lambda (e-rand) (ev e-rand '() s g parent)) e-rands))
                  (proc (eval (string->symbol x) ns)))
              ;(printf "~v: primitive app ~v on ~v\n" e x d-rands)
              (apply proc d-rands)))))))
    ((«car» _ (and e-id («id» _ x)))
     (let ((d (lookup-path x (cons 'car access) s g parent)))
       (printf "-> ~v\n" d)
       d))
    ((«cdr» _ (and e-id («id» _ x)))
     (let ((d (lookup-path x (cons 'cdr access) s g parent)))
       (printf "-> ~v\n" d)
       d))
    ((«cons» _ ar dr)
         (match access
           ('() s)
           (`(car . ,access2) (ev ar access2 s g parent))
           (`(cdr . ,access2) (ev dr access2 s g parent))))
    ))

(define (graph-find g s dir e κ)
  (let graph-fw ((s* (dir s g)))
    (match s*
      (#f #f)
      ((state (== e) (== κ))
       s*)
      (_
       (graph-fw (dir s* g))))))

(define (graph-find-fw g s e κ)
  (graph-find g s successor e κ))

(define (graph-find-bw g s e κ)
  (graph-find g s predecessor e κ))

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
        ((«let» _ _ _ _)
         (ast-helper (graph-find-bw g s pa κ)))
        ((«letrec» _ (and e-decl («id» _ (== x))) _ _)
         (binding x e-decl κ))
        ((«letrec» _ _ _ _)
         (ast-helper (graph-find-bw g s pa κ)))
        ((«app» _ _ _)
         (ast-helper (graph-find-bw g s pa κ)))
        ((«if» _ _ _ _)
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
        (#f (binding x #f #f))))) ; no static decl found

  (define (find-lambda s pa) ; s should eval body expr
    ;(printf "find-lambda ~v ~v\n" s pa)
    (let ((s* (predecessor s g)))
      (match s*
        ((state («app» _ e-rator _) _)
         (ev e-rator '() s* g parent)))))

  (let ((res (ast-helper s)))
    (printf "looked up static ~v = ~v\n" x res)
    res))

(define (lookup-dynamic b s g parent)
  (printf "lookup-dynamic ~v ~v\n" b s)
  (match-let (((binding x e-b κ-b) b))

    (define (lookup-dynamic-helper s)
      (let ((s* (predecessor s g)))
        (match s*
          (#f
           (eval (string->symbol x) ns))
          ((state e κ)
           (match e
             ((«lit» _ _)
              (lookup-dynamic-helper s*))
             ((«lam» _ _ _)
              (lookup-dynamic-helper s*))
             ((«let» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (ev e-init '() s g parent)
                  (lookup-dynamic-helper s*)))
             ((«let» _ _ _ _)
              (lookup-dynamic-helper s*))
             ((«letrec» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (ev e-init '() s g parent)
                  (lookup-dynamic-helper s*)))
             ((«letrec» _ _ _ _)
              (lookup-dynamic-helper s*))
             ((«set!» _ («id» _ (== x)) e-update)
              (let ((b* (lookup-static x s* g parent)))
                (if (equal? b b*)
                    (ev e-update '() s* g parent)
                    (lookup-dynamic-helper s*))))
             ((«set!» _ _ _)
              (lookup-dynamic-helper s*))
             ((«id» _ _)
              (lookup-dynamic-helper s*))
             ((«if» _ _ _ _)
              (lookup-dynamic-helper s*))
             ((«app» _ _ _)
              (if (and (body-expression? (state-e s) parent) ; s* is compound call, s is proc entry
                       (equal? (state-κ s) κ-b))
                  (let* ((e-proc (parent (state-e s)))
                         (xs («lam»-x e-proc)))
                    (let param-loop ((xs xs) (e-args («app»-aes e)))
                      (if (null? xs)
                          (lookup-dynamic-helper s*)
                          (if (equal? (car xs) e-b)
                              (ev (car e-args) '() s* g parent)
                              (param-loop (cdr xs) (cdr e-args))))))
                  (lookup-dynamic-helper s*)))
             ((«set-car!» _ _ _)
              (lookup-dynamic-helper s*))
             ((«car» _ _)
              (lookup-dynamic-helper s*))
             ((«cdr» _ _)
              (lookup-dynamic-helper s*))
             ((«cons» _ _ _)
              (lookup-dynamic-helper s*))
             ))
          )))

    (lookup-dynamic-helper s)))

(define (lookup-variable x s g parent)
  (printf "lookup-variable ~v ~v\n" x s)
  (let ((b (lookup-static x s g parent)))
    (lookup-dynamic b s g parent)))

(define (lookup-path x access s g parent)
  (printf "lookup-path ~v ~v ~v\n" x access s)
  (let ((b (lookup-static x s g parent)))
    (let ((b-root (lookup-root-expression b access s g parent)))
      (printf "root of ~v ~v is ~v\n" b access b-root)
      (lookup-dynamic2 b-root s g parent))))

(define (dobido e access s g parent)
  (printf "dobido ~v ~v ~v\n" e access s)
  (match e
    ((«cons» _ e-car e-cdr)
     (match access
       ((cons 'car access*)
        (if («id»? e-car)
            (let ((b (lookup-static («id»-x e-car) s g parent)))
              (lookup-root-expression b access* s g parent))
            (cons e-car (state-κ s))))
       ((cons 'cdr access*)
        (if («id»? e-cdr)
            (let ((b (lookup-static («id»-x e-cdr) s g parent)))
              (lookup-root-expression b access* s g parent))
            (cons e-cdr (state-κ s))))
       ))
    ((«car» _ («id» _ x-car))
     (let ((b (lookup-static x-car s g parent)))
       (lookup-root-expression b (cons 'car access) s g parent)))
    ((«cdr» _ («id» _ x-cdr))
     (let ((b (lookup-static x-cdr s g parent)))
       (lookup-root-expression b (cons 'cdr access) s g parent)))
    ((«id» _ x)
     (let ((b (lookup-static x s g parent)))
       (lookup-root-expression b access s g parent)))
    ((«app» _ e-rator e-rands)
     (let ((s* (successor (successor s g) g)))
       (dobido (state-e s*) access s* g parent)))
    ))

(define (lookup-root-expression b access s g parent)
  (printf "lookup-root-expression ~v ~v\n" b s)
  (match-let (((binding x e-b κ-b) b))

    (define (lookup-root-expression-helper s)
      (let ((s* (predecessor s g)))
        (match s*
          (#f (error "no root expression found"))
          ((state e κ)
           (match e
             ((«lit» _ _)
              (lookup-root-expression-helper s*))
             ((«lam» _ _ _)
              (lookup-root-expression-helper s*))
             ((«let» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (dobido e-init access s* g parent)
                  (lookup-root-expression-helper s*)))
             ((«let» _ _ _ _)
              (lookup-root-expression-helper s*))
             ((«set!» _ («id» _ x) e-update)
              (let ((b* (lookup-static x s* g parent)))
                (if (equal? b b*)
                    (dobido e-update access s* g parent)
                    (lookup-root-expression-helper s*))))
             ((«set!» _ _ _)
              (lookup-root-expression-helper s*))
             ((«id» _ _)
              (lookup-root-expression-helper s*))
             ((«if» _ _ _ _)
              (lookup-root-expression-helper s*))
             ((«app» _ _ _)
              (if (and (body-expression? (state-e s) parent) ; s* is compound call, s is proc entry
                       (equal? (state-κ s) κ-b))
                  (let* ((e-proc (parent (state-e s)))
                         (xs («lam»-x e-proc)))
                    (let param-loop ((xs xs) (e-args («app»-aes e)))
                      (if (null? xs)
                          (lookup-root-expression-helper s*)
                          (if (equal? (car xs) e-b)
                              (dobido (car e-args) access s* g parent)
                              (param-loop (cdr xs) (cdr e-args))))))
                  (lookup-root-expression-helper s*)))
             ((«set-car!» _ _ _)
              (lookup-root-expression-helper s*))
             ((«set-cdr!» _ _ _)
              (lookup-root-expression-helper s*))
             ((«car» _ _)
              (lookup-root-expression-helper s*))
             ((«cdr» _ _)
              (lookup-root-expression-helper s*))
             ((«cons» _ _ _)
              (lookup-root-expression-helper s*))
             ))
          )))

    (lookup-root-expression-helper s)))


(define (lookup-dynamic2 b-root s g parent)
  (printf "lookup-dynamic2 ~v ~v\n" b-root s)
  (match-let (((cons e-b κ-b) b-root))

    (define (lookup-dynamic2-helper s)
      (let ((s* (predecessor s g)))
        (match s*
          (#f
           (error "unbound root" b-root))
          ((state e κ)
           (match e
             ((«lit» _ _)
              (lookup-dynamic2-helper s*))
             ((«lam» _ _ _)
              (lookup-dynamic2-helper s*))
             ((«let» _ _ _ _)
              (lookup-dynamic2-helper s*))
             ((«letrec» _ _ _ _)
              (lookup-dynamic2-helper s*))
             ((«set!» _ _ _)
              (lookup-dynamic2-helper s*))
             ((«id» _ _)
              (lookup-dynamic2-helper s*))
             ((«if» _ _ _ _)
              (lookup-dynamic2-helper s*))
             ((«app» _ _ _)
              (lookup-dynamic2-helper s*))
             ((«set-car!» _ («id» _ x) e-update)
              (let ((b* (lookup-static x s g parent)))
                (let ((b*-root (lookup-root-expression b* '(car) s* g parent)))
                  (let ((alias? (equal? b*-root b-root)))
                    (printf "binding ~v ~v root ~v alias of ~v ? ~v\n" b* '(car) b*-root b-root alias?)
                    (if alias?
                        (ev e-update '() s* g parent)
                        (lookup-dynamic2-helper s*))))))
             ((«set-cdr!» _ («id» _ x) e-update)
              (let ((b* (lookup-static x s g parent)))
                (let ((b*-root (lookup-root-expression b* '(cdr) s* g parent)))
                  (let ((alias? (equal? b*-root b-root)))
                    (printf "binding ~v ~v root ~v alias of ~v ? ~v\n" b* '(cdr) b*-root b-root alias?)
                    (if alias?
                        (ev e-update '() s* g parent)
                        (lookup-dynamic2-helper s*))))))
             ((«car» _ _)
              (lookup-dynamic2-helper s*))
             ((«cdr» _ _)
              (lookup-dynamic2-helper s*))
             ((«cons» _  (== e-b) (== e-b))
              'TODO)
             ((«cons» _  (== e-b) _)
              (if (equal? κ κ-b)
                  (ev e-b '() s* g parent)
                  (lookup-dynamic2-helper s*)))
             ((«cons» _  _ (== e-b))
              (if (equal? κ κ-b)
                  (ev e-b '() s* g parent)
                  (lookup-dynamic2-helper s*)))
             ((«cons» _ _ _) ; TIODO not all cases handled!
              (lookup-dynamic2-helper s*))
             ))
          )))

    (lookup-dynamic2-helper s)))


(define (explore e)

  (define parent (make-parent e))
  
  ; state -> (set state...)
  (define fwd (hash))
  (define bwd (hash))
  
  ;(define (add-transition graph from to)
  ;  (hash-set graph from (set-add (hash-ref graph from (set)) to)))

  ;(define (add-transition! from to)
  ;  (set! graph (add-transition graph from to)))

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
        ((«let» _ _ _ (== e))
         (cont p κ))
        ((«let» _ _ (== e) e-body)
         (state e-body κ))
        ((«letrec» _ _ _ (== e))
         (cont p κ))
        ((«letrec» _ _ (== e) e-body)
         (state e-body κ))
        ((«set!» _ _ (== e))
         (cont p κ))
        ((«if» _ _ (== e) _)
         (cont p κ))
        ((«if» _ _ _ (== e))
         (cont p κ))
        ((«lam» _ _ (== e))
         (let ((s* (stack-pop (state e κ) κ)))
           ;(printf "pop e ~v κ ~v = ~v\n" e κ κs)
           (cont (state-e s*) (state-κ s*))))
        (#f #f))))
  
  (define (step s)
    (printf "\n#~v\nstep ~v\n" (state->statei s) s)

    (define (step-helper e κ)
      (match e
        ((? ae? e)
         (cont e κ))
        ((«let» _ _ init _)
         (state init κ))
        ((«letrec» _ _ init _)
         (state init κ))
        ((«set!» _ («id» _ x) e-init)
         (cont e κ)) ; only atomic update exps!
        ((«if» _ e-cond e-then e-else)
         (let* ((g (graph fwd bwd #f))
                (d-cond (ev e-cond '() s g parent)))
           (state (if d-cond e-then e-else) κ)))
        ((«app» _ e-rator e-rands)
         (let* ((g (graph fwd bwd #f))
                (d-proc (ev e-rator '() s g parent)))
           (match d-proc
             ((state («lam» _ _ e-body) _)
              (let* ((κ* (count!))
                     (s* (state e-body κ*)))
                s*))
             ((state («set!» _ _ («lam» _ _ e-body)) _)
              (let* ((κ* (count!)) ; CLONE (caused by atomic-only set!)
                     (s* (state e-body κ*)))
                s*))
             ((? procedure?)
              (cont e κ)))))
        ((«cons» _ _ _)
         (cont e κ))
        ((«car» _ _)
         (cont e κ))
        ((«cdr» _ _)
         (cont e κ))
        ((«set-car!» _ _ _) 
         (cont e κ))
        ((«set-cdr!» _ _ _)
         (cont e κ))
        ))

    (match s
      ((state e κ) (step-helper e κ))))

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
    (generate-dot g "grapho")
    (ev (state-e s-end) '() s-end g parent)))

(define (conc-eval e)
  (evaluate e))

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


(module+ main
 (conc-eval
  (compile
   '(let ((o (cons 1 2))) (let ((f (lambda () o))) (let ((u (set-car! o 3))) (let ((w (f))) (car w))))))))


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