#lang racket

(require "general.rkt")
(require "ast.rkt")

(provide conc-eval)
(define ns (make-base-namespace))

;;;;;;;;;;
(define debug-print-in (make-parameter (lambda args #f)))
(define debug-print-out (make-parameter (lambda args #f)))
(define debug-print (make-parameter (lambda args #f)))
;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)

(struct state (e κ) #:transparent)
(struct root (e s) #:transparent)
(struct obj (e s) #:transparent)
; #:property prop:custom-write (lambda (v p w?)
  ;                               (fprintf p "<clo ~v>" (clo-e v))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))

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


(define (graph-eval e s g parent) ; general TODO: every fw movement should be restrained to previous path(s)
  ((debug-print-in) "#~v: graph-eval ~v" (state->statei s) e)

  ; assertion holds: e not id lam lit, s = <e', k>, then e = e'
  ; (when (and (not (or («id»? e) («lam»? e) («lit»? e)))
  ;             (not (equal? e (state-e s))))
  ;   (printf "\n*** ~v ~v\n\n" e (state-e s))
  ;   (error "assertion failed!"))

  (let ((d-result
  (match e
    ((«lit» _ d)
     d)
    ((«id» _ x)
     (let ((b (lookup-var-root x s g parent)))
       (if b
           (eval-var-root x b s g parent)
           (eval (string->symbol x) ns))))
    ((«lam» _ _ _)
     (obj e s))
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
     (obj e s))
    ((«car» _ e-id)
     (let ((r (lookup-path-root e-id 'car s g parent)))
        (eval-path-root r s g parent)))
    ((«cdr» _ e-id)
     (let ((r (lookup-path-root e-id 'cdr s g parent)))
        (eval-path-root r s g parent)))
    )))

    ((debug-print-out) "#~v: graph-eval ~v: ~v" (state->statei s) e (user-print d-result))
    d-result
    ))

(define (lookup-var-root x s g parent)
  ((debug-print-in) "#~v: lookup-var-root ~a" (state->statei s) x)

  (define (ast-helper s)
    (let* ((e (state-e s))
           (κ (state-κ s))
           (pa (parent e)))
      ;(debug-print "#~v: ast-helper x ~v pa ~v" (state->statei s) x (user-print pa))
      (match pa
        ;((«let» _ _ (== e) _)
        ;(ast-helper (state pa κ)))
        ((«let» _ («id» _ (== x)) (and (not (== e)) e-init) _)
         (root e-init (state e-init κ))) ; successor state exists because of `step`
        ((«letrec» _ («id» _ (== x)) e-init _)
         (root e-init (state e-init κ))) ; successor state exists because of `step`
        ((«lam» _ (list xs ...) _) ; s evals body exp e
         (let ((s* (predecessor s g))) ; s* is application of compound
          (match s*
            ((state («app» _ e-rator e-args) _)
             (let param-args-loop ((xs xs) (e-args e-args))
               (if (null? xs)
                   (let* ((d-clo (graph-eval e-rator s* g parent))
                          (s** (obj-s d-clo))) ; s** is where closure was created
                     ((debug-print) "found closure: ~v" d-clo)
                     (ast-helper s**))
                   (let ((e-decl (car xs)))
                     (match e-decl
                        ((«id» _ (== x))
                         (root (car e-args) s*))
                        (_
                         (param-args-loop (cdr xs) (cdr e-args)))))))))))
        (#f #f) ; no parent = no var-root found
        (_
          ; (when (not (hash-has-key? (graph-fwd g) (state pa κ)))
          ;   (printf "\n*** ~v ~v\n" pa κ)
          ;   (error "assertion failed"))
         (ast-helper (state pa κ)))
        )))

  (let ((r (ast-helper s)))
    ((debug-print-out) "#~v: lookup-var-root ~a: ~a" (state->statei s) x (user-print r))
    r))

(define (eval-var-root x b s g parent) ; the `x` param is optimization (see below)
  ((debug-print-in) "#~v: eval-var-root ~a" (state->statei s) (user-print b))

  (match-let (((root e-b s-b) b))

  (define (eval-var-root-helper s)
      ;(debug-print "#~v: eval-var-root-helper" (state->statei s))
      (match s
        ((== s-b)
         (graph-eval e-b s-b g parent))
        ((state e κ)
         (match e
            ((«set!» _ («id» _ (== x)) e-update) ; `== x` avoids looking up var-roots for different name (which can never match `b` anyway)
              (let ((b* (lookup-var-root x s g parent)))
                (if (equal? b b*)
                    (graph-eval e-update s g parent)
                    (eval-var-root-helper (predecessor s g)))))
            (_
              (eval-var-root-helper (predecessor s g)))
            ))
          ))

  (let ((d (eval-var-root-helper (predecessor s g))))
    ((debug-print-out) "#~v: eval-var-root ~a: ~a" (state->statei s) (user-print b) (user-print d))
    d)))

(define (lookup-path-root e-id f s g parent)   
  ((debug-print-in) "#~v: lookup-path-root ~a ~a" (state->statei s) (user-print e-id) f)
  (let ((root 
    (let ((d (graph-eval e-id s g parent)))
      (match* (d f)
        (((obj («cons» _ e-car _) s-root) 'car)
         (root e-car s-root))
        (((obj («cons» _ _ e-cdr) s-root) 'cdr)
         (root e-cdr s-root))
        ; (((state («quo» _ (cons e-car _)) _) 'car)
        ;  (root e-car d))
        ; (((state («quo» _ (cons _ e-cdr)) _) 'cdr)
        ;  (root e-cdr d))
      ))))
    ((debug-print-out) "#~v: lookup-path-root ~a ~a: ~a" (state->statei s) (user-print e-id) f (user-print root))
    root))


(define (eval-path-root r s g parent)
  ((debug-print-in) "#~v: eval-path-root ~a" (state->statei s) (user-print r))
  (match-let
    (((root e-r s-r) r))

    (define (eval-path-root-helper s)
        ;(debug-print "#~v: eval-path-root-helper ~v" (state->statei s) (user-print path-root))
        (match s
          ((== s-r)
           (graph-eval e-r s-r g parent))
          ((state e κ)
           (match e
             ((«set-car!» _ e-id e-update)
              (let ((r* (lookup-path-root e-id 'car s g parent)))
                (if (equal? r r*)
                    (graph-eval e-update s g parent)
                    (eval-path-root-helper (predecessor s g)))))
             ((«set-cdr!» _ e-id e-update)
              (let ((r* (lookup-path-root e-id 'cdr s g parent)))
                (if (equal? r r*)
                    (graph-eval e-update s g parent)
                    (eval-path-root-helper (predecessor s g)))))
             (_ ; TODO not all cases handled yet!
              (eval-path-root-helper (predecessor s g)))
             ))
          ))

    (let ((result (eval-path-root-helper (predecessor s g))))
      ((debug-print-out) "#~v: eval-path-root ~a: ~v" (state->statei s) (user-print r) result)
      result)))

(define (cont s g parent)
  ;(debug-print-in "#~v: cont" (state->statei s))

  (define (cont-helper e κ)
    (let ((p (parent e)))
      ;(debug-print "cont e ~v κ ~v p ~v" e κ p)
      (match p
        ((«let» _ _ (== e) e-body)
         (state e-body κ))
        ((«letrec» _ _ (== e) e-body)
         (state e-body κ))
        ((«lam» _ _ _) ;((«lam» _ _ (== e)) always holds because of parent
         ;(debug-print "pred of #~v is ~v" (state->statei (state e κ)) (user-print (predecessor (state e κ) g)))
         (let ((s* (predecessor (state e κ) g)))
           (cont s* g parent)))
        (#f #f)
        (_ (cont-helper p κ))
        )))
  (let ((s-kont (cont-helper (state-e s) (state-κ s))))
    ;(debug-print-out "#~v: cont: ~v" (state->statei s) (user-print s-kont))
    s-kont))

   
  (define (step s g parent)
    ((debug-print) "\n#~v\nstep ~v" (state->statei s) s)
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
           ((obj («lam» _ _ e-body) _)
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
    ((debug-print) "\n\nEXPLORED with end state ~v" (state->statei s-end))
    ;(generate-dot g "grapho")
    (graph-eval (state-e s-end) s-end g parent)))

(define (conc-eval e)
  (evaluate e))

;;; OUTPUT STUFF
(define (parameterize-full-debug!)
  (define debug-print-level 0)
  (debug-print-in 
    (lambda args
      (apply (debug-print) args)
      (set! debug-print-level (add1 debug-print-level))))
  (debug-print-out
    (lambda args
      (apply (debug-print) args)
      (set! debug-print-level (sub1 debug-print-level))))
  (debug-print
    (lambda args
      (for ((i debug-print-level))
        (display " "))
      (apply printf args)
      (newline))))

(define (user-print d)
  (match d
    ((obj e s) `(obj ,e ,(user-print s)))
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
(define stateis (make-vector 4096))
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
 (parameterize-full-debug!)
 (conc-eval
  (compile
    '(let ((x '(a))) (let ((y '(b))) (let ((u (set! x y))) (car x))))
  )))

; find-lambda
    ;  '(let ((x 0))
    ;     (let ((f (lambda (g) (g))))
    ;       (let ((x 1))
    ;         (let ((h (lambda () x)))
    ;             (f h)))))

; final Agda test (termination: how to reduce trace when if/app move fw?)
      ;  '(let ((x 3))
      ;     (let ((g (lambda (y) y)))
      ;       (let ((f (lambda () (g x))))
      ;         (f))))

(define p1 '(let ((f (lambda (x)
                 (lambda () 
                      x))))
        (let ((g (f 1)))
            (let ((h (f 2)))
                (g))))
)                



(define p2 '(let ((y 999)) (let ((x 123)) (let ((u (if x (set! y 456) (set! y 789)))) y))))

(define p3 '(let ((x (cons 0 1)))
                (let ((y x))
                  (let ((u (set-cdr! y 9)))
                    (cdr x))))
)

(define px '(let ((z (cons 0 1))) 
                 (let ((a (cons 2 3)))
                   (let ((b (cons 4 a))) 
                     (let ((c (cons 5 z)))
                       (let ((u (set! b c)))
                         (let ((d (cdr b)))
                           (let ((v (set-car! z 9)))
                             (car d))))))))
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