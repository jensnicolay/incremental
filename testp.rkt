#lang r5rs

(display 

(let ((r 0))
    (let ((k (lambda (v)
                (lambda () 
                    v))))
        (let ((f (k 1)))
            (let ((g (k 2)))
                (f)))))

)