module Main

import STLC

plus : Expr ctx $ (TNat) :=> ((TNat) :=> (TNat))
plus = Lam (Lam (Rec (Var (Stop)) (Var (Pop (Stop))) (Lam (Lam (Add1 (Var (Stop)))))))


times : Expr ctx $ (TNat) :=> ((TNat) :=> (TNat))
times = Lam (Lam (Rec (Var (Stop)) (Zero) (Lam ((plus) :@ (Var (Pop (Pop (Stop))))))))


id : Expr ctx $ (a) :=> (a)
id = Lam (Var (Stop))


K : Expr ctx $ (a) :=> ((b) :=> (a))
K = Lam (Lam (Var (Pop (Stop))))


whichNat : Expr ctx $ (TNat) :=> ((a) :=> (((TNat) :=> (a)) :=> (a)))
whichNat = Lam (Lam (Lam (Rec (Var (Pop (Pop (Stop)))) (Var (Pop (Stop))) (Lam (Lam ((Var (Pop (Pop (Stop)))) :@ (Var (Pop (Stop)))))))))


iterNat : Expr ctx $ (TNat) :=> ((a) :=> (((a) :=> (a)) :=> (a)))
iterNat = Lam (Lam (Lam (Rec (Var (Pop (Pop (Stop)))) (Var (Pop (Stop))) (Lam (Var (Pop (Stop)))))))


r0 : Expr ?ctx0 ?a0
r0 = normal $ (plus) :@ (Add1 (Add1 (Add1 (Add1 (Add1 (Zero))))))

r1 : Expr ?ctx1 ?a1
r1 = normal $ Lam (((plus) :@ (Var (Stop))) :@ (Add1 (Add1 (Add1 (Add1 (Add1 (Zero)))))))

r2 : Expr ?ctx2 ?a2
r2 = normal $ Lam (((times) :@ (Var (Stop))) :@ (Add1 (Add1 (Add1 (Zero)))))

r3 : Expr ?ctx3 ?a3
r3 = normal $ (((whichNat) :@ (Add1 (Zero))) :@ (Zero)) :@ (Lam (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

r4 : Expr ?ctx4 ?a4
r4 = normal $ (((iterNat) :@ (Add1 (Add1 (Add1 (Zero))))) :@ (Zero)) :@ (Lam (Add1 (Var (Stop))))