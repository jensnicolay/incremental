#lang racket
(require racket/hash)
(require "general.rkt")
(require "ast.rkt")

(provide compile conc-eval parameterize-full-debug!)
(define ns (make-base-namespace))
(random-seed 111)

;;;;;;;;;;
(define debug-print-in #f)
(define debug-print-out #f)
(define debug-print #f)
;;;;;;;;;;

(struct letk (x e ρ) #:transparent)
(struct letreck (x e ρ) #:transparent)

(struct state (e κ) #:transparent)
(struct root (e s) #:transparent)
(struct obj (e s) #:transparent)
; #:property prop:custom-write (lambda (v p w?)
  ;                               (fprintf p "<clo ~v>" (clo-e v))))
; (struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
;                                                                         (equal? (prim-name s1) (prim-name s2))))
;                                                    (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
;                                                    (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))

(struct system (graph end-state parent) #:transparent)
(struct graph (fwd bwd initial) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(graph ~v :initial ~v)" (graph-fwd v) (graph-initial v))))

(define compile (make-compiler))

(define (successor s g)
  (hash-ref (graph-fwd g) s #f))

(define (predecessor s g)
  (hash-ref (graph-bwd g) s #f))

(define (explore e0)

  (define count!
    (let ((counter 0))
      (lambda ()
        (begin0
          counter
          (set! counter (add1 counter))))))

  (define s0 (state e0 (count!)))

  (define Value-prims (hash))
  ;(define Native-prims (hash))
  (define Compiled-prims (hash))

  (define Parent-prim (hash))

  (define (define-value-prim! x proc)
    (set! Value-prims (hash-set Value-prims x proc)))

  ; (define (define-native-prim! x e-lam)
  ;   (let ((e (compile e-lam)))
  ;     (set! Parent-prim (hash-union Parent-prim (parent-map e)))
  ;     (set! Native-prims (hash-set Native-prims x e))))

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
  
  (define (add-transition! from to)
    (set! g (graph (hash-set (graph-fwd g) from to) (hash-set (graph-bwd g) to from) #f)))

  (define (body-expression? e)
    («lam»? (parent e)))

  (define (parent e)
    (hash-ref Parent e #f))

  (define ecache (hash))
  (define (graph-eval e s) ; general TODO: every fw movement should be restrained to previous path(s)
    (and debug-print-in (debug-print-in "#~v: graph-eval ~v" (state->statei s) e))

  ; assertion holds: e not id lam lit, s = <e', k>, then e = e'
  ; (when (and (not (or («id»? e) («lam»? e) («lit»? e)))
  ;             (not (equal? e (state-e s))))
  ;   (printf "\n*** ~v ~v\n\n" e (state-e s))
  ;   (error "assertion failed!"))

  (let ((d-result
    (let ((key (cons e s)))
      (hash-ref ecache key
        (lambda ()
          (let ((d-result
            (match e
              ((«lit» _ d)
              d)
              ((«id» _ x)
              (let ((r (lookup-var-root x s)))
                (if r ; by doing this check here, and not using e-var-root for unbound stuff, prims cannot be redefined
                    (eval-var-root x r s)
                    (eval-primitive x))))
              ((«lam» _ _ _)
              (obj e s))
              ((«quo» _ d)
              d)
              ((«let» _ _ _ e-body)
              (let ((s* (state e-body (state-κ s))))
                (graph-eval e-body s*)))
              ((«letrec» _ _ _ e-body)
              (let ((s* (state e-body (state-κ s))))
                (graph-eval e-body s*)))
              ((«if» _ _ _ _)
              (let ((s* (successor s g)))
                (graph-eval (state-e s*) s*)))
              ((«set!» _ _ _)
              '<unspecified>)
              ((«app» _ e-rator _)
              (let ((κ (state-κ s)))
                (let ((s* (successor s g)))
                  (match s*
                    ((state (? (lambda (e) (body-expression? e)) e-body) _)
                      (graph-eval e-body s*))
                    (_
                      (let ((proc (graph-eval e-rator s)))
                        (proc s))))))) ; only prim
              ((«cons» _ _ _)
              (obj e s))
              ((«car» _ e-id)
              (let ((r (lookup-path-root e-id 'car s)))
                  (eval-path-root r s)))
              ((«cdr» _ e-id)
              (let ((r (lookup-path-root e-id 'cdr s)))
                  (eval-path-root r s)))
              )))
            (set! ecache (hash-set ecache key d-result))
            d-result))))))
    (and debug-print-out (debug-print-out "#~v: graph-eval ~v: ~v" (state->statei s) e (user-print d-result)))
    d-result
    ))

(define lvr (hash))
(define (lookup-var-root x s)
  (and debug-print-in (debug-print-in "#~v: lookup-var-root ~a" (state->statei s) x))

  (define (ast-helper s)
    (let ((key (cons x s)))
      (hash-ref lvr key
        (lambda ()
          (ast-helper% s)))))

  (define (ast-helper% s)
    (let* ((e (state-e s))
           (κ (state-κ s))
           (pa (parent e)))
      ;((debug-print) "#~v: ast-helper x ~v pa ~v" (state->statei s) x (user-print pa))
      (match pa
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
                   (let ((d-clo (graph-eval e-rator s*)))
                     (match d-clo
                       ((obj _ s**) ; s** is where closure was created
                        ;((debug-print) "found closure: ~v" d-clo)
                        (ast-helper s**))
                       (_ #f))) ; prim (in prim?)
                   (let ((e-decl (car xs)))
                     (match e-decl
                        ((«id» _ (== x))
                         (root (car e-args) s*))
                        (_
                         (param-args-loop (cdr xs) (cdr e-args)))))))))))
        ((«lam» _ («id» _ (== x)) _) 
         (let ((s* (predecessor s g)))
          (match s*
            ((state («app» l e-rator e-args) _)
              (let ((e-list (let loop ((e-args e-args))
                              (if (null? e-args)
                                  («lit» (- l) '())
                                  (let ((e-arg (car e-args)))
                                    (let ((l (ast-label e-arg)))
                                      («cons» (- l) e-arg (loop (cdr e-args)))))))))
                (root e-list s*))))))
        (#f #f) ; no parent = no var-root found
        (_
          ; (when (not (hash-has-key? (graph-fwd g) (state pa κ)))
          ;   (printf "\n*** ~v ~v\n" pa κ)
          ;   (error "assertion failed"))
         (ast-helper (state pa κ)))
        )))

  (let ((r
    (let ((key (cons x s)))
      (hash-ref lvr key
        (lambda ()
          (let ((r (ast-helper s)))
            ;(set! lvr (hash-set lvr key r))
            r))))))
    (and debug-print-out (debug-print-out "#~v: lookup-var-root ~a: ~a" (state->statei s) x (user-print r)))
    r))

(define (eval-var-root x r s) ; the `x` param is optimization (see below)
  (and debug-print-in (debug-print-in "#~v: eval-var-root ~a" (state->statei s) (user-print r)))

  (match-let (((root e-r s-r) r)) 

  (define (eval-var-root-helper s)
      ;((debug-print)"#~v: eval-var-root-helper" (state->statei s))
      (match s
        ((== s-r)
         (graph-eval e-r s-r))
        ((state e κ)
         (match e
            ((«set!» _ («id» _ (== x)) e-update) ; `== x` avoids looking up var-roots for different name (which can never match `b` anyway)
              (let ((r* (lookup-var-root x s)))
                (if (equal? r r*)
                    (graph-eval e-update s)
                    (eval-var-root-helper (predecessor s g)))))
            (_
              (eval-var-root-helper (predecessor s g)))
            ))
          ))

  (let ((d (eval-var-root-helper (predecessor s g))))
    (and debug-print-out (debug-print-out "#~v: eval-var-root ~a: ~a" (state->statei s) (user-print r) (user-print d)))
    d)))

(define lpr (hash))
(define (lookup-path-root e-id f s)   
  (and debug-print-in (debug-print-in "#~v: lookup-path-root ~a ~a" (state->statei s) (user-print e-id) f))

  (let ((root
    (let ((key (list e-id f s)))
      (hash-ref lpr key
        (lambda ()
          (let ((r 
            (let ((d (graph-eval e-id s)))
              (match* (d f)
                (((obj («cons» _ e-car _) s-root) 'car)
                (root e-car s-root))
                (((obj («cons» _ _ e-cdr) s-root) 'cdr)
                (root e-cdr s-root))
                ;;
                ; (((obj (cons e-car _) s-root) 'car)
                ;  (root e-car s-root))
                ; (((obj (cons _ e-cdr) s-root) 'cdr)
                ;  (root e-cdr s-root))
              ))))
            ;(set! lpr (hash-set lpr key r))
            r))))))
    (and debug-print-out (debug-print-out "#~v: lookup-path-root ~a ~a: ~a" (state->statei s) (user-print e-id) (user-print root)))
    root))


(define (eval-path-root r s)
  (and debug-print-in (debug-print-in "#~v: eval-path-root ~a" (state->statei s) (user-print r)))
  (match-let
    (((root e-r s-r) r))

    (define (eval-path-root-helper s)
        ;(debug-print "#~v: eval-path-root-helper ~v" (state->statei s) (user-print path-root))
        (match s
          ((== s-r)
           (graph-eval e-r s-r))
          ((state e κ)
           (match e
             ((«set-car!» _ e-id e-update)
              (let ((r* (lookup-path-root e-id 'car s)))
                (if (equal? r r*)
                    (graph-eval e-update s)
                    (eval-path-root-helper (predecessor s g)))))
             ((«set-cdr!» _ e-id e-update)
              (let ((r* (lookup-path-root e-id 'cdr s)))
                (if (equal? r r*)
                    (graph-eval e-update s)
                    (eval-path-root-helper (predecessor s g)))))
             (_ ; TODO not all cases handled yet!
              (eval-path-root-helper (predecessor s g)))
             ))
          ))

    (let ((result (eval-path-root-helper (predecessor s g))))
      (and debug-print-out (debug-print-out "#~v: eval-path-root ~a: ~v" (state->statei s) (user-print r) result))
      result)))

  (define (cont s)
    (and debug-print-in (debug-print-in "#~v: cont" (state->statei s)))

    (define (cont-helper e κ)
      (let ((p (parent e)))
        ;((debug-print) "cont e ~v κ ~v p ~v" e κ p)
        (match p
          ((«let» _ _ (== e) e-body)
          (state e-body κ))
          ((«letrec» _ _ (== e) e-body)
          (state e-body κ))
          ((«lam» _ _ _) ;((«lam» _ _ (== e)) always holds because of parent
          (if (parent p) ; for prims!
              (begin
                ;((debug-print) "pred of #~v is ~v" (state->statei (state e κ)) (user-print (predecessor (state e κ) g)))
                (let ((s* (predecessor (state e κ) g)))
                  (cont s*)))
              #f)) ; 'unconnected' prim lam
          (#f #f)
          (_ (cont-helper p κ))
          )))
    (let ((s-kont (cont-helper (state-e s) (state-κ s))))
      (and debug-print-out (debug-print-out "#~v: cont: ~v" (state->statei s) (user-print s-kont)))
      s-kont))

(define (eval-primitive x)
  (let ((proc (hash-ref Value-prims x #f)))
    (if proc
        (lambda (s)
          (match s
            ((state («app» _ _ e-rands) _)
            (let ((d-rands (map (lambda (e-rand) (graph-eval e-rand s)) e-rands)))
              (apply proc d-rands)))))
        (let ((obj (hash-ref Compiled-prims x #f)))
          (if obj
            obj
            (error "unbound variable" x))))))

  (define (step s)
    (and debug-print (debug-print "#~v: step ~a" (state->statei s) (ast->string (state-e s))))
    (match-let (((state e κ) s))
      (match e
        ((«let» _ _ init _)
         (state init κ))
        ((«letrec» _ _ init _)
         (state init κ))
        ((«if» _ e-cond e-then e-else)
        (let ((d-cond (graph-eval e-cond s)))
          (state (if d-cond e-then e-else) κ)))
        ((«app» _ e-rator e-rands)
        (let ((d-proc (graph-eval e-rator s)))
          (match d-proc
            ((obj («lam» _ _ e-body) _)
              (let* ((κ* (count!))
                    (s* (state e-body κ*)))
                s*))
            ((? procedure?)
              (cont s)))))
        (_ (cont s))
      )))

  (define (explore! s)
    (let ((s* (step s)))
      (if s*
          (begin
            ;(printf "TRANS ~v -> ~v\n" (state->statei s) (set-map succs state->statei))
            (add-transition! s s*)
            (explore! s*))
          s)))

  (define s-end (explore! s0))

  (and debug-print (debug-print "EXPLORED ~v -> ~v" (state->statei (graph-initial g)) (state->statei s-end)))

  (define (dispatcher msg)
    (match msg
      (`(graph) (graph (graph-fwd g) (graph-bwd g) s0))
      (`(s-end) s-end)
      (`(evaluate) (graph-eval (state-e s-end) s-end))
    ))
  
  dispatcher)
      

(define (conc-eval e)
  ((explore e) `(evaluate)))

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

(define (user-print d)
  (match d
    ((obj e s) (format "(obj ~v ~a)" e (user-print s)))
    ((state e κ) (format "#~v" (state->statei d)))
    ((root e s) (format "(root ~v ~a)" e (user-print s)))
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
  (format "~a | ~a" (ast->string (state-e s)) (state-κ s)))

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
 ;(parameterize-full-debug!)
 (conc-eval
  (compile
      (file->value "test/primtest.scm")
  )))
