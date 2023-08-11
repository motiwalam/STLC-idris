(claim plus (-> Nat Nat Nat))
(define plus
    (lambda (x y)
      (rec y x (lambda (_ n) (add1 n)))) 
)

(claim times (-> Nat Nat Nat))
(define times
    (lambda (x y)
        (rec y 0 (lambda (_) (plus x)))))

(claim id (-> a a))
(define id (lambda (x) x))

(claim K (-> a b a))
(define K
    (lambda (x y) x))

(plus 5)
(lambda (n) (plus n 5))

(lambda (n) (times n 3))

(claim whichNat
    (-> Nat a (-> Nat a) a))
(define whichNat
    (lambda (n b s)
        (rec n b (lambda (n-1 _) (s n-1)))))

(claim iterNat
    (-> Nat a (-> a a) a))
(define iterNat
    (lambda (n b f)
        (rec n b (lambda (_) f))))

(whichNat 1 0 (lambda (_) 69))

(iterNat 3 0 (lambda (n) (add1 n)))