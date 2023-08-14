; a simple hello world program to get you started

; a function that takes a Nat n and returns the pair (n, 'hello-world)
(claim hello-world
  (-> Nat (Pair Nat Atom)))
(define hello-world
  (lambda (n)
    (cons n 'hello-world)))

; any top-level expression which isn't a "claim" or a "define" is evaluated and the result is printed
(hello-world 0)
(hello-world 1)
(hello-world 2)
