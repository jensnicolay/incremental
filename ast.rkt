#lang racket
(provide (all-defined-out))

(struct «lit» (l v) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "~a" («lit»-v v))))
(struct «id» (l x) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "~a" («id»-x v))))
(struct «quo» (l e) #:transparent)

(struct «lam» (l x e) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(lambda ~a ~a)" («lam»-x v) («lam»-e v))))
(struct «app» (l ae aes) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "~a" (cons («app»-ae v) («app»-aes v)))))

(struct «let» (l x e0 e1) #:transparent
    #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(let ((~a ~a)) ~a)" («let»-x v) («let»-e0 v) («let»-e1 v))))

(struct «letrec» (l x e0 e1) #:transparent
      #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(letrec ((~a ~a)) ~a)" («letrec»-x v) («letrec»-e0 v) («letrec»-e1 v))))

(struct «if» (l ae e0 e1) #:transparent
    #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(if ~a ~a ~a)" («if»-ae v) («if»-e0 v) («if»-e1 v))))

(struct «set!» (l x ae) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(set! ~a ~a)" («set!»-x v) («set!»-ae v))))

(struct «car» (l x) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(car ~a)" («car»-x v))))

(struct «cdr» (l x) #:transparent 
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(cdr ~a)" («cdr»-x v))))

(struct «set-car!» (l x ae) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(set-car! ~a ~a)" («set-car!»-x v) («set-car!»-ae v))))

(struct «set-cdr!» (l x ae) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(set-cdr! ~a ~a)" («set-cdr!»-x v) («set-cdr!»-ae v))))

(struct «cons» (l ae1 ae2) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(cons ~a ~a)" («cons»-ae1 v) («cons»-ae2 v))))

(struct «vector-ref» (l x ae) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(vector-ref ~a ~a)" («vector-ref»-x v) («vector-ref»-ae v))))

(struct «vector-set!» (l x ae1 ae2) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(vector-set! ~a ~a ~a)" («vector-set!»-x v) («vector-set!»-ae1 v) («vector-set!»-ae2 v))))

(struct «make-vector» (l ae1 ae2) #:transparent
        #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "(make-vector ~a ~a)" («make-vector»-ae1 v) («make-vector»-ae2 v))))


(define (compile e)
  (define l -1)
  (define (tag!)
    (set! l (add1 l))
    l)
  (define (compile2 e)
    (match e
      ((? symbol? v) («id» (tag!) (symbol->string v)))
      ((? boolean? v) («lit» (tag!) v))
      ((? number? v) («lit» (tag!) v))
      ((? string? v)(«lit» (tag!) v))
      ((? char? v) («lit» (tag!) v))
      (`(quote ,e) (compile-quote e))
      (`(lambda ,x ,e) («lam» (tag!) (map compile2 x) (compile2 e)))
      (`(if ,ae ,e1 ,e2) («if» (tag!) (compile2 ae) (compile2 e1) (compile2 e2)))
      (`(let ((,x ,e0)) ,e1) («let» (tag!) (compile2 x) (compile2 e0) (compile2 e1)))
      (`(letrec ((,x ,e0)) ,e1) («letrec» (tag!) (compile2 x) (compile2 e0) (compile2 e1)))
      (`(set! ,x ,ae) («set!» (tag!) (compile2 x) (compile2 ae)))
      (`(car ,x) («car» (tag!) (compile2 x)))
      (`(cdr ,x) («cdr» (tag!) (compile2 x)))
      (`(cons ,ae1 ,ae2) («cons» (tag!) (compile2 ae1) (compile2 ae2)))
      (`(set-car! ,x ,ae) («set-car!» (tag!) (compile2 x) (compile2 ae)))
      (`(set-cdr! ,x ,ae) («set-cdr!» (tag!) (compile2 x) (compile2 ae)))        
      (`(vector-ref ,x ,ae) («vector-ref» (tag!) (compile2 x) (compile2 ae)))
      (`(vector-set! ,x ,ae1 ,ae2) («vector-set!» (tag!) (compile2 x) (compile2 ae1) (compile2 ae2)))
      (`(make-vector ,ae1 ,ae2) («make-vector» (tag!) (compile2 ae1) (compile2 ae2)))
      (`(,rator . ,rands) («app» (tag!) (compile2 rator) (map compile2 rands)))
      ((? «id»?) e)
      ((? «lam»?) e)
      ((? «let»?) e)
      ((? «letrec»?) e)
      ((? «if»?) e)
      ((? «set!»?) e)
      ((? «quo»?) e)
      ((? «app»?) e)
      ((? «lit»?) e)
      (_ (error "cannot handle expression" e))))
  (define (compile-quote e)
    (match e
      ((cons e-car e-cdr) («cons» (tag!) (compile-quote e-car) (compile-quote e-cdr)))
      ('() («lit» (tag!) e))
      ((? symbol? x) («lit» (tag!) x))
      (_ (compile2 e))))
  (compile2 e))
         
(define (ae? e)
  (match e
    ((«lit» _ _) #t)
    ((«id» _ _) #t)
    ((«lam» _ _ _) #t)
    ((«quo» _ e) (not (pair? e))) 
    (_ #f)))

(define (children e)
  (match e
    ((«id» _ _) (set))
    ((«lit» _ _) (set))
    ((«lam» _ x e) (set-add (list->set x) e))
    ((«let» _ x e0 e1) (set x e0 e1))
    ((«letrec» _ x e0 e1) (set x e0 e1))
    ((«if» _ ae e1 e2) (set ae e1 e2))
    ((«car» _ x) (set x))
    ((«cdr» _ x) (set x))
    ((«set!» _ x ae) (set x ae))
    ((«set-car!» _ x ae) (set x ae))
    ((«set-cdr!» _ x ae) (set x ae))
    ((«cons» _ ae1 ae2) (set ae1 ae2))
    ((«make-vector» _ ae1 ae2) (set ae1 ae2))
    ((«vector-ref» _ x ae) (set x ae))
    ((«vector-set!» _ x ae1 ae2) (set x ae1 ae2))
    ((«quo» _ _) (set))
    ((«app» _ rator rands) (set-add (list->set rands) rator))
    (_ (error "cannot handle expression" e))))

;(define (parent e ast)
;  (let ((cs (children ast)))
;    (if (set-member? cs e)
;        ast
;        (let loop ((cs cs))
;          (if (set-empty? cs)
;              #f
;              (let ((p (parent e (set-first cs))))
;                (or p (loop (set-rest cs)))))))))


(define (parent-map ast)
  (define (traverse-ast S W)
    (if (set-empty? W)
        S
        (let* ((e (set-first W))
               (E* (children e))
               (S* (for/fold ((S S)) ((e* E*))
                     (hash-set S e* e)))
               (W* (set-union (set-rest W) E*)))
          (traverse-ast S* W*))))
  (traverse-ast (hash) (set ast)))

(define (make-parent ast)
  (let ((P (parent-map ast)))
    (lambda (e)
      (hash-ref P e #f))))

(define (nodes ast) (for/fold ((cs (list ast))) ((c (children ast))) (append cs (nodes c))))

(define (free e)
  (define (f e env)
    (match e
      ((«id» _ x) (if (set-member? env x)
                      (set)
                      (set x)))
      ((«lam» _ x e) (f e (set-union env (list->set (map «id»-x x)))))
      ((«let» _ x e0 e1) (set-union (f e0 env) (f e1 (set-add env («id»-x x)))))
      ((«letrec» _ x e0 e1) (set-union (f e0 (set-add env («id»-x x))) (f e1 (set-add env («id»-x x)))))
      ((«if» _ ae e1 e2) (set-union (f ae env) (f e1 env) (f e2 env)))
      ((«set!» _ x ae) (set-union (f x env) (f ae env)))
      ((«car» _ x) (f x env))
      ((«cdr» _ x) (f x env))
      ((«set-car!» _ x ae) (set-union (f x env) (f ae env)))
      ((«set-cdr!» _ x ae) (set-union (f x env) (f ae env)))
      ((«cons» _ ae1 ae2) (set-union (f ae1 env) (f ae2 env)))
      ((«make-vector» _ ae1 ae2) (set-union (f ae1 env) (f ae2 env)))
      ((«vector-ref» _ x ae) (set-union (f x env) (f ae env)))
      ((«vector-set!» _ x ae1 ae2) (set-union (f x env) (f ae1 env) (f ae2 env)))
      ((«quo» _ _) (set))
      ((«app» _ rator rands) (set-union (f rator env) (for/fold ((xs (set))) ((rand rands)) (set-union xs (f rand env)))))
      ((«id» _ _) (set))
      ((«lit» _ _) (set))
      (_ (error "cannot handle expression" e))))
  (f e (set)))

(module+ main

  (free (compile (file->value "test/browse.scm")))

  ; (compile
  ;   ''(a b c)
  ; )
  
)


