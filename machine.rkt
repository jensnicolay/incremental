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
(struct state (e κ) #:transparent)
(struct binding (e κ) #:transparent)
(struct root (e s) #:transparent)
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

(define (successor s g)
  (hash-ref (graph-fwd g) s #f))

(define (predecessor s g)
  (hash-ref (graph-bwd g) s #f))

(define (body-expression? e parent)
  («lam»? (parent e)))


;(define (graph-eval e s g parent)
;  (graph-eval-path e '() s g parent))
  
(define (graph-eval e s g parent) ; general TODO: every fw movement should be restrained to previous path(s)
  (debug-print-in "#~v: graph-eval ~v" (state->statei s) e)

  ; assertion holds: e not id lam lit, s = <e', k>, then e = e'
  ; (when (and (not (or («id»? e) («lam»? e) («lit»? e)))
  ;             (not (equal? e (state-e s))))
  ;   (printf "\n*** ~v ~v\n\n" e (state-e s))
  ;   (error "assertion failed!"))

;(eval (string->symbol x) ns)

  (let ((d-result
  (match e
    ((«lit» _ d)
     d)
    ((«id» _ x)
     (lookup-var x s g parent))
    ((«lam» _ e-params e-body)
     (clo e s))
    ((«quo» _ (cons _ _))
     s)
    ((«quo» _ d)
     d)
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
    ((«cons» _ _ _)
      s)
    ((«car» _ (and e-id («id» _ x)))
     (let ((path-root (lookup-path-root x '(car) s g parent)))
       (eval-path-root path-root s g parent)))
    ((«cdr» _ (and e-id («id» _ x)))
     (let ((path-root (lookup-path-root x '(cdr) s g parent)))
       (eval-path-root path-root s g parent)))
    )))

    (debug-print-out "#~v: graph-eval ~v: ~v" (state->statei s) e (user-print d-result))
    d-result
    ))


(define (lookup-var x s g parent)
  (debug-print-in "#~v: lookup-var ~v" (state->statei s) x)
  (let ((b (lookup-binding x s g parent)))
    (match-let (((binding e-b κ-b) b))

    (define (lookup-var-helper s)
      (let ((s* (predecessor s g)))
        ;(debug-print "#~v: lookup-var-helper #~v" (state->statei s) (state->statei s*))
        (match s*
          (#f (eval (string->symbol x) ns))
          ((state e κ)
          (match e
            ((«let» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (graph-eval e-init s g parent)
                  (lookup-var-helper s*)))
            ((«letrec» _ (== e-b) e-init _)
              (if (equal? κ κ-b)
                  (graph-eval e-init s g parent)
                  (lookup-var-helper s*)))
            ((«set!» _ («id» _ (== x)) e-update)
              (let ((b* (lookup-binding x s* g parent)))
                (if (equal? b b*)
                    (graph-eval e-update s* g parent)
                    (lookup-var-helper s*))))
            ((«app» _ _ _)
              (if (and (body-expression? (state-e s) parent) ; s* is compound call, s is proc entry
                      (equal? (state-κ s) κ-b))
                  (let* ((e-proc (parent (state-e s)))
                        (xs («lam»-x e-proc)))
                    (let param-loop ((xs xs) (e-args («app»-aes e)))
                      (if (null? xs)
                          (lookup-var-helper s*)
                          (if (equal? (car xs) e-b)
                              (graph-eval (car e-args) s* g parent)
                              (param-loop (cdr xs) (cdr e-args))))))
                  (lookup-var-helper s*)))
            (_
              (lookup-var-helper s*))
            ))
          )))

    (let ((d (lookup-var-helper s)))
      (debug-print-out "#~v: lookup-var ~v: ~a" (state->statei s) x (user-print d))
      d))))

(define (lookup-path-root x field-path s g parent)
  (debug-print-in "#~v: lookup-path-root ~v ~v" (state->statei s) x field-path)

  (let ((var-binding (lookup-binding x s g parent)))
    (match-let (((binding e-b κ-b) var-binding))

      (define (lookup-path-root-helper field-path s g parent)
        (let* ((s* (predecessor s g)))
          (match s*
            (#f #f)
            ((state e κ)
             ;(debug-print "#~v: lookup-path-root-helper #~v ~v ~v" (state->statei s) (state->statei s*) x field-path)
              (match e
                ; ((«id» _ x)
                ; (lookup-path-root x field-path s g parent))
                ; ((«quo» _ e)
                ; (let loop ((e e) (field-path field-path))
                ;   (match field-path
                ;     ((cons 'car field-path*)
                ;     (if (pair? (car e))
                ;         (loop (car e) field-path*)
                ;         (root (car e) s)))
                ;     ((cons 'cdr field-path*)
                ;     (if (pair? (cdr e))
                ;         (loop (cdr e) field-path*)
                ;         (root (cdr e) s)))
                ;     ('() (root e s))
                ;     )))
                ((«app» _ _ _)
                  (if (and (body-expression? (state-e s) parent) ; s* is compound call, s is proc entry
                          (equal? (state-κ s) κ-b))
                      (let* ((e-proc (parent (state-e s)))
                            (xs («lam»-x e-proc)))
                        (let param-loop ((xs xs) (e-args («app»-aes e)))
                          (if (null? xs)
                              (lookup-path-root-helper field-path s* g parent)
                              (if (equal? (car xs) e-b)
                                  (if (null? field-path)
                                      (root (car e-args) s*)
                                      (let ((d (graph-eval (car e-args) s* g parent)))
                                        (match d
                                          ((state e* κ*)
                                          (match e*
                                              ((«cons» _ e-car e-cdr)
                                                (match field-path
                                                  ((cons 'car '())
                                                  (root e-car d))
                                                  ((cons 'cdr '())
                                                  (root e-cdr d))
                                                  ((list-rest field-path* ... 'car '())
                                                  (lookup-path-root («id»-x e-car) field-path* d g parent))
                                                  ((list-rest field-path* ... 'cdr '())
                                                  (lookup-path-root («id»-x e-cdr) field-path* d g parent)))))))))                                      
                                  (param-loop (cdr xs) (cdr e-args))))))
                      (lookup-path-root-helper field-path s* g parent)))    

                ((«let» _ (== e-b) («car» _ («id» _ y)) _)
                  (if (equal? κ κ-b)
                      (lookup-path-root y (append field-path '(car)) s* g parent)
                      (lookup-path-root-helper field-path s* g parent)))
                ((«let» _ (== e-b) («cdr» _ («id» _ y)) _)
                  (if (equal? κ κ-b)
                      (lookup-path-root y (append field-path '(cdr)) s* g parent)
                      (let ((s* (predecessor s g)))
                        (lookup-path-root-helper field-path s* g parent))))
                ; ((«let» _ (== e-b) («id» _ y) _)
                ;   (if (equal? κ κ-b)
                ;       (lookup-path-root y field-path s* g parent)
                ;       (lookup-path-root-helper field-path s* g parent)))
                ((«let» _ (== e-b) e-init _)
                  (if (equal? κ κ-b) 
                      (if (null? field-path)
                          (root e-init (successor s* g))
                          (let ((d (graph-eval e-init (successor s* g) g parent)))
                            (match d
                              ((state e* κ*)
                               (match e*
                                  ((«cons» _ e-car e-cdr)
                                    (match field-path
                                      ((cons 'car '())
                                      (root e-car d))
                                      ((cons 'cdr '())
                                      (root e-cdr d))
                                      ((list-rest field-path* ... 'car '())
                                      (lookup-path-root («id»-x e-car) field-path* d g parent))
                                      ((list-rest field-path* ... 'cdr '())
                                      (lookup-path-root («id»-x e-cdr) field-path* d g parent)))))))))
                      (lookup-path-root-helper field-path s* g parent)))
                ((«letrec» _ (== e-b) e-init _)
                  (if (equal? κ κ-b)
                      (if (null? field-path)
                          (root e-init (successor s* g))
                          (let ((d (graph-eval e-init (successor s* g) g parent)))
                            (match d
                              ((state e* κ*)
                               (match e*
                                  ((«cons» _ e-car e-cdr)
                                    (match field-path
                                      ((cons 'car '())
                                      (root e-car d))
                                      ((cons 'cdr '())
                                      (root e-cdr d))
                                      ((list-rest field-path* ... 'car '())
                                      (lookup-path-root («id»-x e-car) field-path* d g parent))
                                      ((list-rest field-path* ... 'cdr '())
                                      (lookup-path-root («id»-x e-cdr) field-path* d g parent)))))))))
                      (lookup-path-root-helper field-path s* g parent)))
                ((«set!» _ («id» _ (== x)) e-update)
                  (let ((b* (lookup-binding x s* g parent)))
                    (if (equal? var-binding b*)
                        (if (null? field-path)
                            (root e-update s*)
                            (lookup-path-root («id»-x e-update) field-path s* g parent))
                        (lookup-path-root-helper field-path s* g parent))))
                ((«set-car!» _ («id» _ (== x)) («id» _ y))
                  (let ((b* (lookup-binding x s* g parent)))
                    (if (and (equal? var-binding b*)
                          (eq? (last field-path) 'car))
                      (lookup-path-root y (drop-right field-path 1) s* g parent)
                      (lookup-path-root-helper field-path s* g parent))))
                ((«set-cdr!» _ («id» _ (== x)) («id» _ y))
                  (let ((b* (lookup-binding x s* g parent)))
                    (if (and (equal? var-binding b*)
                          (eq? (last field-path) 'cdr))
                      (lookup-path-root y (drop-right field-path 1) s* g parent)
                      (lookup-path-root-helper field-path s* g parent))))
                (_ (lookup-path-root-helper field-path s* g parent))

              )))))

      (let ((path-root (lookup-path-root-helper field-path s g parent)))
        (debug-print-out "#~v: lookup-path-root ~v ~v: ~a" (state->statei s) x field-path (user-print path-root))
        (unless (or (root? path-root) (not path-root))
          (error "not a root" path-root))
        path-root))))

(define (lookup-binding x s g parent)
  (debug-print-in "#~v: lookup-binding ~v" (state->statei s) x)

  (define (ast-helper s)
    (let* ((e (state-e s))
           (κ (state-κ s))
           (pa (parent e)))
      ;(printf "\tast-helper ~v e ~v pa ~v\n" x e pa)
      (match pa
        ;((«let» _ _ (== e) _)
        ;(ast-helper (state pa κ)))
        ((«let» _ (and v («id» _ (== x))) (not (== e)) _)
         (binding v κ))
        ((«letrec» _ (and v («id» _ (== x))) _ _)
         (binding v κ))
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

          ; (when (not (hash-has-key? (graph-fwd g) (state pa κ)))
          ;   (printf "\n*** ~v ~v\n" pa κ)
          ;   (error "assertion failed"))

         (ast-helper (state pa κ)))
        ))) ; no binding found

  (define (lookup-closure e κ)

        ; this assertion fails!!! (e, κ) does not need to be a state!
        ;  (when (not (hash-has-key? (graph-fwd g) (state e κ)))
        ;    (printf "\n*** ~v ~v\n" e κ)
        ;    (error "assertion failed"))

    ;(printf "\tlookup-closure ~v ~v\n" e κ)
    (let ((s* (predecessor (state e κ) g)))
      (match s*
        ((state («app» _ e-rator _) _)
         (let ((d-clo (graph-eval e-rator s* g parent)))
           (debug-print "found closure: ~v" d-clo)
           (clo-s d-clo))))
      ))

  (let ((res (ast-helper s)))
    (debug-print-out "#~v: lookup-binding ~v: ~v" (state->statei s) x res)
    res))

(define (eval-path-root path-root s g parent) ; l-dynamic
  (debug-print-in "#~v: eval-path-root ~a" (state->statei s) (user-print path-root))
  (match-let (((root e-b s-b) path-root))

    (define (eval-path-root-helper s)
        ;(debug-print "#~v: eval-path-root-helper ~v" (state->statei s) (user-print path-root))
        (match s
;          (#f
;           (error "unbound root" root))
          ((== s-b)
           (graph-eval e-b s g parent))
          ((state e κ)
           (match e
             ((«set-car!» _ («id» _ x) e-update)
              (let* ((path-root* (lookup-path-root x '(car) s g parent)))
                (if (equal? path-root* path-root)
                    (graph-eval e-update s g parent)
                    (eval-path-root-helper (predecessor s g)))))
             ((«set-cdr!» _ («id» _ x) e-update)
              (let* ((path-root* (lookup-path-root x '(cdr) s g parent)))
                (if (equal? path-root* path-root)
                    (graph-eval e-update s g parent)
                    (eval-path-root-helper (predecessor s g)))))
             (_ ; TODO not all cases handled yet!
              (eval-path-root-helper (predecessor s g)))
             ))
          ))

    (let ((result (eval-path-root-helper (predecessor s g))))
      (debug-print-out "#~v: eval-path-root ~a: ~v" (state->statei s) (user-print path-root) result)
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
        ((«lam» _ _ _) ;((«lam» _ _ (== e)) always holds because of parent
         (let ((s* (predecessor (state e κ) g)))
           (cont s* g parent)))
        (#f #f)
        (_ (cont-helper p κ))
        )))

  (cont-helper (state-e s) (state-κ s)))
   
  (define (step s g parent)
    (debug-print "\n#~v\nstep ~v" (state->statei s) s)
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
    (debug-print "\n\nEXPLORED with end state ~v" (state->statei s-end))
    ;(generate-dot g "grapho")
    (graph-eval (state-e s-end) s-end g parent)))

(define (conc-eval e)
  (evaluate e))

;;; OUTPUT STUFF

(define debug-print-level 0)
(define (debug-print-in . args)
  (apply debug-print args)
  (set! debug-print-level (add1 debug-print-level)))
(define (debug-print-out . args)
  (set! debug-print-level (sub1 debug-print-level))
  (apply debug-print args))
(define (debug-print . args)
  (for ((i debug-print-level))
    (display " "))
  (apply printf args)
  (newline))

(define (user-print d)
  (match d
    ((clo e s) `(clo ,e ,(user-print s)))
    ((state e κ) (format "#~v" (state->statei d)))
    ((root e s) `(root ,e ,(user-print s)))
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

        '(let ((f (lambda () (lambda (x) (* x x))))) (let ((g (f))) (g 4)))

      ; '(let ((f (lambda (a b)
      ;                  (cons a b))))
      ;     (let ((g (lambda (p)
      ;                 p)))
      ;       (let ((h (lambda (p)
      ;                  (set-car! p 9))))
      ;         (let ((p (f 0 1)))
      ;           (let ((q (g p)))
      ;             (let ((u (set-car! q 4)))
      ;               (let ((x1 (car p)))
      ;                 (let ((v (h p)))
      ;                   (let ((x2 (car q)))
      ;                     (+ x1 x2))))))))))

      ;  '(let ((f (lambda (x)
      ;                     (let ((x1 (car x)))
      ;                       (let ((x2 (cdr x)))
      ;                         (+ x1 x2))))))
      ;            (let ((cell (cons 2 3)))
      ;              (let ((u (set-car! cell 0)))
      ;                (f cell))))

  )))

; find-lambda
    ;  '(let ((x 0))
    ;     (let ((f (lambda (g) (g))))
    ;       (let ((x 1))
    ;         (let ((h (lambda () x)))
    ;             (f h)))))


(define p1 '(let ((z (cons 0 1))) 
                 (let ((a (cons 2 3)))
                   (let ((b (cons 4 a))) 
                     (let ((c (cons 5 z)))
                       (let ((u (set! b c)))
                         (let ((d (cdr b)))
                           (let ((v (set-car! z 9)))
                             (car d))))))))
)

(define p2 '(let ((f (lambda (x)
                 (lambda () 
                      x))))
        (let ((g (f 1)))
            (let ((h (f 2)))
                (g))))
)                

  ; '(let ((x 0))
  ;   (let ((f (lambda (g)
  ;               g)))
  ;     (let ((a (lambda () x)))
  ;       (let ((b (lambda () 1)))
  ;           (let ((fa (f a)))
  ;             (let ((fb (f b)))
  ;               (fa)))))))

                      
(define p-let-rule '(let ((f (lambda (x) x))) (let ((v (f 999))) v)))
           

;;; INTERESTING CASE is when the update exp of a set! can be non-atomic: first encountered set! when walking back is not the right one!
;;;; THEREFORE: we only allow aes as update exps
;;;(test '(let ((x 123)) (let ((y (set! x (set! x 456)))) x)) 'undefined)
;;;(test '(let ((x 123)) (let ((y (set! x (let ((u (set! x 456))) 789)))) x)) 789)

;;; SCHEME ERROR when setting before init
;;; (test '(letrec ((x (let ((u (set! x 123))) 456))) x) 456)