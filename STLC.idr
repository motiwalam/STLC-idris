module STLC

%default covering

infixr 0 :=>
public export
data Ty
    = TNat
    | (:=>) Ty Ty
Show Ty where
    show TNat = "Nat"
    show (a :=> b) = "(-> \{show a} \{show b})"

public export
data Context : Type where
    Nil : Context
    (::) : Ty -> Context -> Context

public export
data DeBruijn : Context -> Ty -> Type where
    Stop : DeBruijn (a :: r) a
    Pop  : DeBruijn ctx a -> DeBruijn (_ :: ctx) a

infixl 0 :@
public export
data Expr : Context -> Ty -> Type where
    Var : DeBruijn ctx a -> Expr ctx a
    Lam : Expr (a :: ctx) b -> Expr ctx (a :=> b)
    (:@) : Expr ctx (a :=> b) -> Expr ctx a -> Expr ctx b
    Zero : Expr ctx TNat
    Add1 : Expr ctx TNat -> Expr ctx TNat
    Rec : Expr ctx TNat -> Expr ctx a -> Expr ctx (TNat :=> a :=> a) -> Expr ctx a
    The : (a : Ty) -> Expr ctx a -> Expr ctx a

public export
show_expr : {ctx : Context} -> Expr ctx a -> String
show_expr e = showHelper [] e where
    gensym : List String -> String
    gensym l = "x\{show $ length l}"

    db_list : DeBruijn _ _ -> List String -> Maybe String
    db_list _ [] = Nothing
    db_list Stop (x :: r) = Just x
    db_list (Pop k) (x :: r) = db_list k r

    showHelper : List String -> Expr _ _ -> String
    showHelper _ Zero = "0"
    showHelper used (Var x) = case db_list x used of
                                Just n  => n
                                Nothing => "@error"

    showHelper used (Lam f) = let x = gensym used in "(lambda (\{x}) \{showHelper (x::used) f})"
    showHelper used (f :@ x) = "(\{showHelper used f} \{showHelper used x})"
    showHelper used (Add1 n) = "(add1 \{showHelper used n})"
    showHelper used (Rec n b s) = "(rec \{showHelper used n} \{showHelper used b} \{showHelper used s})"
    showHelper used (The a e) = "(the \{show a} \{showHelper used e})"

mutual
    data Val : Context -> Ty -> Type where
        VNeutral : Neutral ctx a -> Val ctx a
        VClosure : Env ctx' ctx -> Expr (a :: ctx) b -> Val ctx' (a :=> b)

        VZero : Val ctx TNat
        VAdd1 : Val ctx TNat -> Val ctx TNat

    data Neutral : Context -> Ty -> Type where
        NVar : DeBruijn ctx a -> Neutral ctx a
        NApp : Neutral ctx (a :=> b) -> Val ctx a -> Neutral ctx b
        NRec : Neutral ctx TNat -> Val ctx a -> Val ctx (TNat :=> a :=> a) -> Neutral ctx a
    
    infixr 0 :::
    data Env : Context -> Context -> Type where
        Empty : Env ctx' Nil
        (:::) : Val ctx' a -> Env ctx' ctx -> Env ctx' (a :: ctx)

lookup : DeBruijn ctx a -> Env ctx' ctx -> Val ctx' a
lookup Stop (a ::: r) = a
lookup (Pop k) (a ::: r) = lookup k r

mutual
    doApply : Val ctx (a :=> b) -> Val ctx a -> Val ctx b
    doApply (VClosure env f) x = eval (x ::: env) f
    doApply (VNeutral f) x = VNeutral $ NApp f x

    doRec : Val ctx TNat -> Val ctx a -> Val ctx (TNat :=> a :=> a) -> Val ctx a
    doRec VZero b s = b
    doRec (VAdd1 n) b s = doApply (doApply s n)
                                  (doRec n b s)
    doRec (VNeutral n) b s = VNeutral $ NRec n b s

    public export
    eval : Env ctx' ctx -> Expr ctx a -> Val ctx' a
    eval env (Var x) = lookup x env 
    eval env (Lam f) = VClosure env f
    eval env (f :@ x) = doApply (eval env f) (eval env x)
    eval env Zero = VZero
    eval env (Add1 n) = VAdd1 $ eval env n
    eval env (The _ e) = eval env e
    eval env (Rec n b s) = doRec (eval env n) (eval env b) (eval env s)


infix 0 :<=
data (:<=) : Context -> Context -> Type where
    Refl : ctx :<= ctx
    Weak : ctx :<= ctx' -> (a :: ctx) :<= ctx'
    Lift : ctx :<= ctx' -> (a :: ctx) :<= (a :: ctx')

infixl 0 :.
(:.) : ctx :<= ctx' -> ctx' :<= ctx'' -> ctx :<= ctx''
Refl :. x = x
(Weak x) :. y = Weak (x :. y)
(Lift x) :. Refl = Lift x
(Lift x) :. (Weak y) = Weak (x :. y)
(Lift x) :. (Lift y) = Lift (x :. y)

mutual
    weakenDeBruijn : ctx :<= ctx' -> DeBruijn ctx' a -> DeBruijn ctx a
    weakenDeBruijn Refl x = x
    weakenDeBruijn (Weak x) k = Pop $ weakenDeBruijn x k
    weakenDeBruijn (Lift x) Stop = Stop
    weakenDeBruijn (Lift x) (Pop k) = Pop $ weakenDeBruijn x k

    weakenVal : ctx :<= ctx' -> Val ctx' a -> Val ctx a
    weakenVal _ VZero = VZero
    weakenVal x (VAdd1 n) = VAdd1 $ weakenVal x n
    weakenVal Refl v = v
    weakenVal x (VClosure env f) = VClosure (weakenEnv x env) f
    weakenVal x (VNeutral n) = VNeutral $ weakenNeutral x n

    weakenEnv : ctx :<= ctx' -> Env ctx' c -> Env ctx c
    weakenEnv _ Empty = Empty
    weakenEnv Refl e = e
    weakenEnv x (h ::: r) = weakenVal x h ::: weakenEnv x r

    weakenNeutral : ctx :<= ctx' -> Neutral ctx' a -> Neutral ctx a
    weakenNeutral x (NVar i) = NVar $ weakenDeBruijn x i
    weakenNeutral x (NApp f a) = NApp (weakenNeutral x f) (weakenVal x a)
    weakenNeutral x (NRec n b s) = NRec (weakenNeutral x n) (weakenVal x b) (weakenVal x s)
    

mutual
    readback : Val ctx a -> Expr ctx a
    readback (VNeutral w) = nereadback w
    readback v@(VClosure _ _) = Lam $ readback $ doApply (weakenVal (Weak Refl) v) $ VNeutral (NVar Stop)
    readback VZero = Zero
    readback (VAdd1 n) = Add1 $ readback n

    nereadback : Neutral ctx a -> Expr ctx a
    nereadback (NVar x) = Var x
    nereadback (NApp f x) = (nereadback f) :@ (readback x)
    nereadback (NRec n b s) = Rec (nereadback n) (readback b) (readback s)


ide : (c : Context) -> Env c c
ide Nil = Empty
ide (a :: c) = (VNeutral $ NVar Stop) ::: (weakenEnv (Weak Refl) (ide c))

public export
normal : {ctx : Context} -> Expr ctx a -> Expr ctx a
normal {ctx} t = readback (eval (ide ctx) t)
