(define-value-prim! "=" =)
(define-value-prim! "zero?" zero?)
(define-value-prim! "<" <)
(define-value-prim! "<=" <=)
(define-value-prim! ">" >)
(define-value-prim! ">=" >=)
(define-value-prim! "+" +)
(define-value-prim! "-" -)
(define-value-prim! "*" *)
(define-value-prim! "/" /)
(define-value-prim! "even?" even?)
(define-value-prim! "odd?" odd?)
(define-value-prim! "null?" null?)
(define-value-prim! "eq?" equal?)
(define-value-prim! "number->string" number->string)
(define-value-prim! "symbol->string" symbol->string)
(define-value-prim! "string->symbol" string->symbol)
(define-value-prim! "not" not)
(define-value-prim! "remainder" remainder)
(define-value-prim! "string-ref" string-ref)

(define-value-prim! "pair?"
  (lambda (d-rand . _)
    (match d-rand
      ((obj («cons» _ _ _) _)
        #t)
      (_ #f))))

(define-compile-prim! "list"
  '(lambda (x)
    (cons x 2)))

    ; (define-native-prim! "eqv?"
    ;   (lambda (_ __ d-rands)
    ;     (set (for*/fold ((d ⊥)) ((w1 (γ (car d-rands))) (w2 (γ (cadr d-rands))))
    ;            (⊔ d (match* (w1 w2)
    ;                   (((addr a) (addr a))
    ;                    (α #t))
    ;                   (((addr _) (addr _))
    ;                    (α #f))
    ;                   ((_ _)
    ;                    (α-eq? w1 w2))))))))

  
    ; (define-native-prim! "error"
    ;   (lambda _ (set)))
    
    ; (define-native-prim! "display"
    ;   (lambda (_ __ d-rands)
    ;     (printf "~v\n" d-rands)
    ;     (set (α 'undefined))))    
    
    
    ; (define-native-prim! "cons"
    ;   (lambda (e-app κ d-rands)
    ;     (let ((a (alloc e-app κ)))
    ;       (store-alloc! a (α (cons (car d-rands) (cadr d-rands))))
    ;       (set (α (addr a))))))

    ; (define (list-alloc-helper! d-rands e-rands κ)
    ;   (if (null? d-rands)
    ;       (α '())
    ;       (let ((d-cdr (list-alloc-helper! (cdr d-rands) (cdr e-rands) κ)))
    ;         (let ((a (alloc (car e-rands) κ)))
    ;           (store-alloc! a (α (cons (car d-rands) d-cdr)))
    ;           (α (addr a))))))    

    ; (define-native-prim! "car"
    ;   (lambda (_ κ d-rands)
    ;     (set (for/fold ((d ⊥)) ((a (in-set (γ (car d-rands)))) #:when (addr? a))
    ;            (for/fold ((d d)) ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
    ;              (⊔ d (car w)))))))

    ; (define-native-prim! "set-car!"
    ;   (lambda (_ κ d-rands)
    ;     (let ((d (cadr d-rands)))
    ;       (for ((a (in-set (γ (car d-rands)))) #:when (addr? a))
    ;         (for ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
    ;           (store-update! (addr-a a) (α (cons d (cdr w))))))
    ;       (set (α 'undefined)))))

    ; (define-native-prim! "cdr"
    ;   (lambda (_ κ d-rands)
    ;     (set (for/fold ((d ⊥)) ((a (in-set (γ (car d-rands)))) #:when (addr? a))
    ;            (for/fold ((d d)) ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
    ;              (⊔ d (cdr w)))))))
    
    ; (define-native-prim! "set-cdr!"
    ;   (lambda (_ κ d-rands)
    ;     (let ((d (cadr d-rands)))
    ;       (for ((a (in-set (γ (car d-rands)))) #:when (addr? a))
    ;         (for ((w (in-set (γ (store-lookup (addr-a a))))) #:when (pair? w))
    ;           (store-update! (addr-a a) (α (cons (car w) d)))))
    ;       (set (α 'undefined)))))


    ; (define-native-prim! "make-vector"
    ;   (lambda (e-app κ d-rands)
    ;     (let* ((a (alloc e-app κ))
    ;            (num (car d-rands))
    ;            (lt-proc (lambda (x y)
    ;                       (for/fold ((result ⊥)) ((prim2 (γ (cdr (assoc "<" lat-glob)))))
    ;                         (⊔ result ((prim2-proc prim2) x y))))) ; TODO check whether we can use conc +1 and then α
    ;            (add-proc (lambda (x y)
    ;                        (for/fold ((result ⊥)) ((prim2 (γ (cdr (assoc "+" lat-glob)))))
    ;                          (⊔ result ((prim2-proc prim2) x y)))))
    ;            (init (cadr d-rands))
    ;            (h (hash)))
    ;       (let loop ((h h) (i (α 0)))
    ;         (if (and (true? (lt-proc i num)) (not (hash-has-key? h i)))
    ;             (loop (hash-set h i init) (add-proc i (α 1)))
    ;             (let ((v (α h)))
    ;               (store-alloc! a v)
    ;               (set (α (addr a)))))))))

    ; (define-native-prim! "vector"
    ;   (lambda (e-app κ d-rands)
    ;     (let* ((a (alloc e-app 'TODO))
    ;            (num (length d-rands))
    ;            (h (hash)))
    ;       (let loop ((h h) (d-rands d-rands) (i 0))
    ;         (if (null? d-rands)
    ;             (let ((v (α h)))
    ;               (store-alloc! a v)
    ;               (set (α (addr a))))
    ;             (loop (hash-set h (α i) (car d-rands)) (cdr d-rands) (add1 i)))))))

    ; (define-native-prim! "vector-ref"
    ;   (lambda (_ κ d-rands)
    ;     (let ((index (cadr d-rands)))
    ;       (let ((v (for/fold ((v ⊥)) ((w (γ (car d-rands))))
    ;                  (match w
    ;                    ((addr a)
    ;                     (for/fold ((v v)) ((ww (γ (store-lookup a))))
    ;                       (if (hash? ww)
    ;                           (for/fold ((v v)) (((key val) ww))
    ;                             (if (or (⊑ index key) (⊑ key index) )
    ;                                 (⊔ v val)
    ;                                 v))
    ;                           v)))
    ;                    (_ v )))))
    ;         (set v)))))

    ; (define-native-prim! "vector-set!"
    ;   (lambda (_ κ d-rands)
    ;     (let ((v1 (car d-rands))
    ;           (v2 (cadr d-rands))
    ;           (v3 (caddr d-rands)))
    ;       (for ((w (in-set (γ v1))) #:when (addr? w))
    ;         (let ((a (addr-a w)))
    ;           (for ((ww (in-set (γ (store-lookup a)))))
    ;             (when (hash? ww)
    ;               (store-update! a (α (hash-set ww v2 v3)))))))
    ;       (set (α 'undefined)))))

    ; (define-native-prim! "vector-length"
    ;   (lambda (_ κ d-rands)
    ;     (if (= (length d-rands) 1)
    ;         (let ((add-proc (lambda (x y)
    ;                           (for/fold ((result ⊥)) ((prim2 (in-set (γ (cdr (assoc "+" lat-glob))))))
    ;                             (⊔ result ((prim2-proc prim2) x y)))))
    ;               (lt-proc (lambda (x y)
    ;                     (for/fold ((result ⊥)) ((prim2 (in-set (γ (cdr (assoc "<" lat-glob))))))
    ;                       (⊔ result ((prim2-proc prim2) x y))))))
    ;           (let ((v (for/fold ((v ⊥)) ((w (in-set (γ (car d-rands)))))
    ;                      (match w
    ;                        ((addr a)
    ;                         (for/fold ((v v)) ((ww (γ (store-lookup a))))
    ;                           (if (hash? ww)
    ;                               (⊔ v (for/fold ((n (α 0))) ((i (in-set (hash-keys ww))))
    ;                                      (let ((ii (add-proc i (α 1))))
    ;                                        (if (lt-proc ii n)
    ;                                            n
    ;                                            ii))))
    ;                               v)))
    ;                        (_ v)))))
    ;             (set v)))
    ;         (set))))
    
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;    
    

    (define-compile-prim! "vector-copy"
      '(lambda (v)
         (let ((l (vector-length v)))
           (let ((v2 (make-vector l #f)))
             (letrec ((loop (lambda (i)
                              (let ((c (< i l)))
                                (if c
                                    (let ((x (vector-ref v i)))
                                      (let ((_ (vector-set! v2 i x)))
                                        (let ((ii (+ i 1)))
                                          (loop ii))))
                                    v2)))))
               (loop 0))))))
        
    (define-compile-prim! "equal?"
      '(lambda (x1 x2)
         (let ((_b_t2 (pair? x1)))
           (if _b_t2
               (let ((_b_t3 (pair? x2)))
                 (if _b_t3
                     (let ((_b_t4 (car x1)))
                       (let ((_b_t5 (car x2)))
                         (let ((_b_t6 (equal? _b_t4 _b_t5)))
                           (if _b_t6
                               (let ((_b_t7 (cdr x1)))
                                 (let ((_b_t8 (cdr x2)))
                                   (equal? _b_t7 _b_t8)))
                               #f))))
                     #f))
               (eq? x1 x2)))))

    (define-compile-prim! "cadr"
      '(lambda (p)
         (let ((x (cdr p)))
           (car x))))

    (define-compile-prim! "cddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (cdr x))))

    (define-compile-prim! "caadr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (car x)))
             (car y)))))

    (define-compile-prim! "caddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (cdr x)))
             (car y)))))

    (define-compile-prim! "cadddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (cdr x)))
             (let ((z (cdr y)))
               (car z))))))

    (define-compile-prim! "cdadr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (car x)))
             (cdr y)))))

    (define-compile-prim! "cdddr"
      '(lambda (p)
         (let ((x (cdr p)))
           (let ((y (cdr x)))
             (cdr y)))))

    (define-compile-prim! "member"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((e (equal? a v)))
                   (if e
                       lst
                       (let ((d (cdr lst)))
                         (member v d)))))))))

    (define-compile-prim! "memv"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((e (eqv? a v)))
                   (if e
                       lst
                       (let ((d (cdr lst)))
                         (memv v d)))))))))

    (define-compile-prim! "memq"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((e (eq? a v)))
                   (if e
                       lst
                       (let ((d (cdr lst)))
                         (memq v d)))))))))

    (define-compile-prim! "assq"
      '(lambda (v lst)
         (let ((c (null? lst)))
           (if c
               #f
               (let ((a (car lst)))
                 (let ((key (car a)))
                   (let ((e (equal? key v)))
                     (if e
                         a
                         (let ((d (cdr lst)))
                           (assq v d))))))))))

    (define-compile-prim! "append"
      '(lambda (lst1 lst2)
         (let ((c (null? lst1)))
           (if c
               lst2
               (let ((d (cdr lst1)))
                 (let ((l (append d lst2)))
                   (let ((a (car lst1)))
                     (cons a l))))))))
                 
    (define-compile-prim! "length"
      '(lambda (lst)
         (let ((c (null? lst)))
           (if c
               0
               (let ((d (cdr lst)))
                 (let ((n (length d)))
                   (+ 1 n)))))))
    
    (define-compile-prim! "reverse"
      '(lambda (l)
         (letrec ((reverse-acc (lambda (l acc)
                                 (let ((c (null? l)))
                                   (if c
                                       acc
                                       (let ((u (cdr l)))
                                         (let ((v (car l)))
                                           (let ((w (cons v acc)))
                                             (reverse-acc u w)))))))))
           (reverse-acc l '()))))

    (define-compile-prim! "map"
      '(lambda (f lst)
         (let ((c (null? lst)))
           (if c
               lst
               (let ((a (car lst)))
                 (let ((x (f a)))
                   (let ((d (cdr lst)))
                     (let ((l (map f d)))
                       (cons x l)))))))))

    (define-compile-prim! "for-each"
      '(lambda (f lst)
         (let ((c (null? lst)))
           (if c
               'undefined
               (let ((a (car lst)))
                 (let ((_ (f a)))
                   (let ((d (cdr lst)))
                     (for-each f d))))))))    
    
    (define-compile-prim! "list?"
      '(lambda (v)
         (let ((c (null? v)))
           (if c
               #t
               (pair? v)))))

    (define-compile-prim! "list->string"
      '(lambda (lst) ; TODO `(apply string lst)` [requires apply]
         (let ((c (null? lst)))
           (if c
               ""
               (let ((ch (car lst)))
                 (let ((st (string ch)))
                   (let ((suf (cdr lst)))
                     (let ((sufst (list->string suf)))
                       (string-append st sufst)))))))))
    
    (define-compile-prim! "vector->list"
      '(lambda (vec)
           (letrec ((loop (lambda (i acc)
                            (let ((c (= i -1)))
                              (if c
                                  acc
                                  (let ((el (vector-ref vec i)))
                                    (let ((acc2 (cons el acc)))
                                      (let ((ii (- i 1)))
                                        (loop ii acc2)))))))))
             (let ((l (vector-length vec)))
               (let ((ll (- l 1)))
                 (loop ll '()))))))
    
    (define-compile-prim! "list->vector"
      '(lambda (lst)
         (letrec ((down (lambda (lst i)
                          (let ((c (null? lst)))
                            (if c
                                (let ((v (make-vector i #f)))
                                  v)
                                (let ((a (car lst)))
                                  (let ((d (cdr lst)))
                                    (let ((ii (+ i 1)))
                                      (let ((v (down d ii)))
                                        (let ((_ (vector-set! v i a)))
                                          v))))))))))
           (down lst 0))))
