(letrec ((_append0 (lambda (_l0 _m0) (let ((_17 (null? _l0)))
                                       (if _17 _m0 (let ((_18 (car _l0)))
                                                     (let ((_19 (cdr _l0)))
                                                       (let ((_20 (_append0 _19 _m0))) (cons _18 _20)))))))))
  (letrec ((_super-merge-n0 (lambda (_lsts0 _n0)
                              (letrec ((_geef-n+rest0 (lambda (_lst0 _n1)
                                                        (let ((_10 (= 0 _n1)))
                                                          (let ((_11 (if _10 #t (null? _lst0))))
                                                            (if _11
                                                                (let ((_12 '()))
                                                                  (cons _12 _lst0))
                                                                (let ((_res0 (let ((_15 (cdr _lst0)))
                                                                               (let ((_16 (- _n1 1)))
                                                                                 (_geef-n+rest0 _15 _16)))))
                                                                  (let ((_first0 (car _res0)))
                                                                    (let ((_rest0 (cdr _res0)))
                                                                      (let ((_13 (car _lst0)))
                                                                        (let ((_14 (cons _13 _first0)))
                                                                          (cons _14 _rest0))))))))))))
                                (let ((_3 (null? _lsts0)))
                                  (if _3
                                      '() (let ((_g-n+rest0 (let ((_9 (car _lsts0))) (_geef-n+rest0 _9 _n0)))) (let ((_first1 (car _g-n+rest0)))
                                                                                                                 (let ((_rest1 (cdr _g-n+rest0)))
                                                                                                                   (let ((_4 (cdr _lsts0)))
                                                                                                                     (let ((_5 (null? _rest1)))
                                                                                                                       (let ((_6 (if _5 _rest1 (list _rest1))))
                                                                                                                         (let ((_7 (_append0 _4 _6)))
                                                                                                                           (let ((_8 (_super-merge-n0 _7 _n0)))
                                                                                                                             (_append0 _first1 _8)))))))))))))))
    (let ((_0 '((a b c d e f) (g h i j k) (l m n o p q) (r s t u v w)))) (let ((_1 (_super-merge-n0 _0 3))) (let ((_2 '(a b c g h i l m n r s t d e f j k o p q u v w)))
                                                                                                              (equal? _1 _2))))))