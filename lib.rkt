(claim which-nat
    (-> Nat a (-> Nat a) a))
(define which-nat
    (lambda (n b s)
        (rec
            n
            b
            (lambda (n-1 _) (s n))
            )))

(claim iter-nat
    (-> Nat a (-> a a) a))
(define iter-nat
    (lambda (n b s)
        (rec
            n
            b
            (lambda (_) s))))

(claim id (-> a a))
(define id (lambda (x) x))

(claim succ (-> Nat Nat))
(define succ
    (lambda (n) (add1 n)))

(claim pred (-> Nat Nat))
(define pred
    (lambda (n) (which-nat n 0 id)))

(claim + (-> Nat Nat Nat))
(define +
    (lambda (m n)
        (iter-nat n m succ)))

(claim * (-> Nat Nat Nat))
(define *
    (lambda (n m) (iter-nat n 0 (+ m))))

(claim gauss
    (-> Nat Nat))
(define gauss
    (lambda (n)
        (rec
            n
            0
            (lambda (n-1 acc) (+ acc n-1)))))

(gauss 7)