module Main

import STLC

whichminus_stlcnat : Expr ctx $ (TNat) :=> ((a) :=> (((TNat) :=> (a)) :=> (a)))
whichminus_stlcnat = Lam (Lam (Lam (Rec (Var (S (S (Z)))) (Var (S (Z))) (Lam (Lam ((Var (S (S (Z)))) :@ (Var (S (Z)))))))))


iterminus_stlcnat : Expr ctx $ (TNat) :=> ((a) :=> (((a) :=> (a)) :=> (a)))
iterminus_stlcnat = Lam (Lam (Lam (Rec (Var (S (S (Z)))) (Var (S (Z))) (Lam (Var (S (Z)))))))


id : Expr ctx $ (a) :=> (a)
id = Lam (Var (Z))


sgn : Expr ctx $ ?sgn_t
sgn = Lam ((((whichminus_stlcnat) :@ (Var (Z))) :@ (Zero)) :@ (Lam (Add1 (Zero))))


cosgn : Expr ctx $ ?cosgn_t
cosgn = Lam ((((whichminus_stlcnat) :@ (Var (Z))) :@ (Add1 (Zero))) :@ (Lam (Zero)))


succ : Expr ctx $ ?succ_t
succ = Lam (Add1 (Var (Z)))


pred : Expr ctx $ ?pred_t
pred = Lam ((((whichminus_stlcnat) :@ (Var (Z))) :@ (Zero)) :@ (id))


mu : Expr ctx $ ?mu_t
mu = Lam (Lam ((((iterminus_stlcnat) :@ (Var (S (Z)))) :@ ((cosgn) :@ ((Var (Z)) :@ (Zero)))) :@ (Lam ((((iterminus_stlcnat) :@ ((cosgn) :@ ((Var (S (Z))) :@ (Var (Z))))) :@ (Var (Z))) :@ (succ)))))


plus_stlc : Expr ctx $ ?plus_stlc_t
plus_stlc = Lam (Lam ((((iterminus_stlcnat) :@ (Var (S (Z)))) :@ (Var (Z))) :@ (succ)))


minus_stlc : Expr ctx $ ?minus_stlc_t
minus_stlc = Lam (Lam ((((iterminus_stlcnat) :@ (Var (Z))) :@ (Var (S (Z)))) :@ (pred)))


times_stlc : Expr ctx $ ?times_stlc_t
times_stlc = Lam (Lam ((((iterminus_stlcnat) :@ (Var (S (Z)))) :@ (Zero)) :@ ((plus_stlc) :@ (Var (Z)))))


pow : Expr ctx $ ?pow_t
pow = Lam (Lam ((((iterminus_stlcnat) :@ (Var (Z))) :@ (Add1 (Zero))) :@ ((times_stlc) :@ (Var (S (Z))))))


gt_stlc : Expr ctx $ ?gt_stlc_t
gt_stlc = Lam (Lam ((sgn) :@ (((minus_stlc) :@ (Var (S (Z)))) :@ (Var (Z)))))


lt_stlc : Expr ctx $ ?lt_stlc_t
lt_stlc = Lam (Lam ((sgn) :@ (((minus_stlc) :@ (Var (Z))) :@ (Var (S (Z))))))


eq_stlceq_stlc : Expr ctx $ ?eq_stlceq_stlc_t
eq_stlceq_stlc = Lam (Lam (((minus_stlc) :@ (Add1 (Zero))) :@ (((plus_stlc) :@ (((minus_stlc) :@ (Var (S (Z)))) :@ (Var (Z)))) :@ (((minus_stlc) :@ (Var (Z))) :@ (Var (S (Z)))))))


slash_stlcslash_stlc : Expr ctx $ ?slash_stlcslash_stlc_t
slash_stlcslash_stlc = Lam (Lam (((mu) :@ (Var (S (Z)))) :@ (Lam (((gt_stlc) :@ (((times_stlc) :@ ((succ) :@ (Var (Z)))) :@ (Var (S (Z))))) :@ (Var (S (S (Z))))))))


percent : Expr ctx $ ?percent_t
percent = Lam (Lam (((minus_stlc) :@ (Var (S (Z)))) :@ (((times_stlc) :@ (Var (Z))) :@ (((slash_stlcslash_stlc) :@ (Var (S (Z)))) :@ (Var (Z))))))


dividesq : Expr ctx $ ?dividesq_t
dividesq = Lam (Lam (((eq_stlceq_stlc) :@ (Zero)) :@ (((percent) :@ (Var (Z))) :@ (Var (S (Z))))))


foldr : Expr ctx $ ((a) :=> ((b) :=> (b))) :=> ((b) :=> ((TList (a)) :=> (b)))
foldr = Lam (Lam (Lam (RecList (Var (Z)) (Var (S (Z))) (Lam (Lam (Lam (((Var (S (S (S (S (S (Z))))))) :@ (Var (S (S (Z))))) :@ (Var (Z)))))))))


append : Expr ctx $ (a) :=> ((TList (a)) :=> (TList (a)))
append = Lam (Lam (RecList (Var (Z)) (LCons (Var (S (Z))) (LNil)) (Lam (Lam (Lam (LCons (Var (S (S (Z)))) (Var (Z))))))))


reverse : Expr ctx $ (TList (a)) :=> (TList (a))
reverse = Lam (RecList (Var (Z)) (LNil) (Lam (Lam (Lam (((append) :@ (Var (S (S (Z))))) :@ (Var (Z)))))))


sum : Expr ctx $ ?sum_t
sum = Lam (Lam (Rec (Var (Z)) ((Var (S (Z))) :@ (Zero)) (Lam (Lam (((plus_stlc) :@ (Var (Z))) :@ ((Var (S (S (S (Z))))) :@ ((succ) :@ (Var (S (Z))))))))))


prod : Expr ctx $ ?prod_t
prod = Lam (Lam (Rec (Var (Z)) ((Var (S (Z))) :@ (Zero)) (Lam (Lam (((times_stlc) :@ (Var (Z))) :@ ((Var (S (S (S (Z))))) :@ ((succ) :@ (Var (S (Z))))))))))


ex : Expr ctx $ ?ex_t
ex = Lam (((prod) :@ (succ)) :@ ((pred) :@ (Var (Z))))


primeq : Expr ctx $ ?primeq_t
primeq = Lam (((eq_stlceq_stlc) :@ (Add1 (Add1 (Zero)))) :@ (((sum) :@ (Lam (((dividesq) :@ (Var (Z))) :@ (Var (S (Z)))))) :@ (Var (Z))))


nthminus_stlcprime : Expr ctx $ ?nthminus_stlcprime_t
nthminus_stlcprime = Lam (Rec (Var (Z)) (Add1 (Add1 (Zero))) (Lam (Lam (((mu) :@ ((succ) :@ ((ex) :@ (Var (Z))))) :@ (Lam (((times_stlc) :@ ((primeq) :@ (Var (Z)))) :@ (((gt_stlc) :@ (Var (Z))) :@ (Var (S (Z))))))))))


r0 : Expr ?ctx0 ?a0
r0 = normal $ (nthminus_stlcprime) :@ (Quote "atom")