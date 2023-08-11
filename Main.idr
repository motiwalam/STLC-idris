module Main

import STLC

which_nat : Expr ctx $ (TNat) :=> ((a) :=> (((TNat) :=> (a)) :=> (a)))
which_nat = Lam (Lam (Lam (Rec (Var (Pop (Pop (Stop)))) (Var (Pop (Stop))) (Lam (Lam ((Var (Pop (Pop (Stop)))) :@ (Var (Pop (Pop (Pop (Pop (Stop))))))))))))


iter_nat : Expr ctx $ (TNat) :=> ((a) :=> (((a) :=> (a)) :=> (a)))
iter_nat = Lam (Lam (Lam (Rec (Var (Pop (Pop (Stop)))) (Var (Pop (Stop))) (Lam (Var (Pop (Stop)))))))


id : Expr ctx $ (a) :=> (a)
id = Lam (Var (Stop))


succ : Expr ctx $ (TNat) :=> (TNat)
succ = Lam (Add1 (Var (Stop)))


pred : Expr ctx $ (TNat) :=> (TNat)
pred = Lam ((((which_nat) :@ (Var (Stop))) :@ (Zero)) :@ (id))


plus : Expr ctx $ (TNat) :=> ((TNat) :=> (TNat))
plus = Lam (Lam ((((iter_nat) :@ (Var (Stop))) :@ (Var (Pop (Stop)))) :@ (succ)))


times : Expr ctx $ (TNat) :=> ((TNat) :=> (TNat))
times = Lam (Lam ((((iter_nat) :@ (Var (Pop (Stop)))) :@ (Zero)) :@ ((plus) :@ (Var (Stop)))))


gauss : Expr ctx $ (TNat) :=> (TNat)
gauss = Lam (Rec (Var (Stop)) (Zero) (Lam (Lam (((plus) :@ (Var (Stop))) :@ (Var (Pop (Stop)))))))


r0 : Expr ?ctx0 ?a0
r0 = normal $ (gauss) :@ (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Add1 (Zero))))))))