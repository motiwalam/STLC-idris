(claim which-nat
    (-> Nat a (-> Nat a) a))
(define which-nat
    (lambda (n b s)
        (rec-nat n b
            (lambda (n-1 _) (s n-1)))))

(claim iter-nat
    (-> Nat a (-> a a) a))
(define iter-nat
    (lambda (n b s)
        (rec-nat n b
            (lambda (_) s))))

(claim id (-> a a))
(define id 
    (lambda (x) x))

(define sgn
    (lambda (n) (which-nat n 0 (lambda (_) 1))))
(define cosgn
    (lambda (n) (which-nat n 1 (lambda (_) 0))))

(define succ 
    (lambda (n) (add1 n)))

(define pred 
    (lambda (n) (which-nat n 0 id)))

(define mu
    (lambda (x p)
        (iter-nat
            x
            (cosgn (p 0)) 
            (lambda (z)
                (iter-nat (cosgn (p z)) z succ)))))

(define +
    (lambda (m n)
        (iter-nat m n succ)))

(define -
    (lambda (m n)
        (iter-nat n m pred)))

(define *
    (lambda (m n)
        (iter-nat m 0 (+ n))))

(define ^
    (lambda (m n)
        (iter-nat n 1 (* m))))

(define >
    (lambda (n m) (sgn (- n m))))

(define <
    (lambda (n m) (sgn (- m n))))

(define ==
  (lambda (n m)
    (- 1 (+ (- n m) (- m n)))))


(define //
    (lambda (n m)
        (mu n (lambda (z) (> (* (succ z) m) n)))))

(define %
    (lambda (n m) (- n (* m (// n m)))))

(define divides?
    (lambda (n m) (== 0 (% m n))))

(claim foldr
    (-> (-> a b b) b (List a) b))
(define foldr
    (lambda (f i l)
        (rec-list
            l
            i
            (lambda (x _ acc)
                (f x acc))
            )))

(claim append
    (-> a (List a) (List a)))
(define append
    (lambda (e l)
        (rec-list
            l
            [e]
            (lambda (x _ acc) (:: x acc))
            )))

(claim reverse
    (-> (List a) (List a)))
(define reverse
    (lambda (l)
        (rec-list
            l
            nil
            (lambda (x _ acc) (append x acc))
            )))



(define sum
    (lambda (f n)
        (rec-nat n (f 0) (lambda (n-1 acc) (+ acc (f (succ n-1)))))))
    
(define prod
    (lambda (f n)
        (rec-nat n (f 0) (lambda (n-1 acc) (* acc (f (succ n-1)))))))

(define ! (lambda (n) (prod succ (pred n))))

(define prime?
    (lambda (p)
        (== 2 (sum (lambda (x) (divides? x p)) p))))

(define nth-prime
    (lambda (n+1)
        (rec-nat
            n+1
            2
            (lambda (n pn)
                (mu (succ (! pn))
                    (lambda (z)
                        (* (prime? z) (> z pn))))))))


(nth-prime 2)
