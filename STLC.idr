module STLC

%default covering

infixr 0 :=>
public export
data Ty
    = TNat
    | Atom
    | (:=>) Ty Ty
    | TPair Ty Ty
    | TList Ty

Show Ty where
    show TNat = "Nat"
    show (a :=> b) = "(-> \{show a} \{show b})"
    show (TPair a b) = "(Pair \{show a} \{show b})"
    show (TList t) = "(List \{show t})"
    show Atom = "Atom"

public export
Context : Type
Context = List Ty

public export
data DeBruijn : Context -> Ty -> Type where
    Z : DeBruijn (a :: r) a
    S : DeBruijn ctx a -> DeBruijn (_ :: ctx) a

infixl 0 :@
public export
data Expr : Context -> Ty -> Type where
    Var : DeBruijn ctx a -> Expr ctx a
    Lam : Expr (a :: ctx) b -> Expr ctx (a :=> b)
    (:@) : Expr ctx (a :=> b) -> Expr ctx a -> Expr ctx b
    Quote : String -> Expr ctx Atom
    Zero : Expr ctx TNat
    Add1 : Expr ctx TNat -> Expr ctx TNat
    Rec : Expr ctx TNat -> Expr ctx a -> Expr ctx (TNat :=> a :=> a) -> Expr ctx a
    Cons : Expr ctx a -> Expr ctx b -> Expr ctx (TPair a b)
    Car : Expr ctx (TPair a b) -> Expr ctx a
    Cdr : Expr ctx (TPair a b) -> Expr ctx b
    LNil : Expr ctx (TList a)
    LCons : Expr ctx a -> Expr ctx (TList a) -> Expr ctx (TList a)
    RecList : Expr ctx (TList a) -> Expr ctx x -> Expr ctx (a :=> (TList a) :=> x :=> x) -> Expr ctx x
    The : (a : Ty) -> Expr ctx a -> Expr ctx a

public export
show_expr : {a : Ty} -> {ctx : Context} -> Expr ctx a -> String
show_expr e = showHelper [] e where
    gensym : List String -> String
    gensym l = "x\{show $ length l}"

    db_list : DeBruijn _ _ -> List String -> Maybe String
    db_list _ [] = Nothing
    db_list Z (x :: r) = Just x
    db_list (S k) (x :: r) = db_list k r

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

    showHelper used (Cons a b) = "(cons \{showHelper used a} \{showHelper used b})"
    showHelper used (Car p) = "(car \{showHelper used p})"
    showHelper used (Cdr p) = "(cdr \{showHelper used p})"

    showHelper used LNil = "nil"
    showHelper used (LCons x xs) = "(:: \{showHelper used x} \{showHelper used xs})"
    showHelper used (RecList xs b s) = "(rec-list \{showHelper used xs} \{showHelper used b} \{showHelper used s})"

    showHelper used (Quote s) = "'\{substr 1 (length s) $ show s}"

mutual
    data Val : Context -> Ty -> Type where
        VNeutral : Neutral ctx a -> Val ctx a
        VClosure : Env ctx' ctx -> Expr (a :: ctx) b -> Val ctx' (a :=> b)

        VZero : Val ctx TNat
        VAdd1 : Val ctx TNat -> Val ctx TNat

        VPair : Val ctx a -> Val ctx b -> Val ctx (TPair a b)

        VNil : Val ctx (TList a)
        VCons : Val ctx a -> Val ctx (TList a) -> Val ctx (TList a)

        VAtom : String -> Val ctx Atom

    data Neutral : Context -> Ty -> Type where
        NVar : DeBruijn ctx a -> Neutral ctx a
        NApp : Neutral ctx (a :=> b) -> Val ctx a -> Neutral ctx b
        NRec : Neutral ctx TNat -> Val ctx a -> Val ctx (TNat :=> a :=> a) -> Neutral ctx a

        NCar : Neutral ctx (TPair a b) -> Neutral ctx a
        NCdr : Neutral ctx (TPair a b) -> Neutral ctx b

        NRecList : Neutral ctx (TList a) -> Val ctx x -> Val ctx (a :=> (TList a) :=> x :=> x) -> Neutral ctx x 
    
    data Env : Context -> Context -> Type where
        Nil : Env ctx' Nil
        (::) : Val ctx' a -> Env ctx' ctx -> Env ctx' (a :: ctx)

lookup : DeBruijn ctx a -> Env ctx' ctx -> Val ctx' a
lookup Z (a :: r) = a
lookup (S k) (a :: r) = lookup k r

mutual
    doApply : Val ctx (a :=> b) -> Val ctx a -> Val ctx b
    doApply (VClosure env f) x = eval (x :: env) f
    doApply (VNeutral f) x = VNeutral $ NApp f x

    doRec : Val ctx TNat -> Val ctx a -> Val ctx (TNat :=> a :=> a) -> Val ctx a
    doRec VZero b s = b
    doRec (VAdd1 n) b s = doApply (doApply s n)
                                  (doRec n b s)
    doRec (VNeutral n) b s = VNeutral $ NRec n b s

    doCar : Val ctx (TPair a b) -> Val ctx a
    doCar (VPair a _) = a
    doCar (VNeutral p) = VNeutral $ NCar p

    doCdr : Val ctx (TPair a b) -> Val ctx b
    doCdr (VPair _ b) = b
    doCdr (VNeutral p) = VNeutral $ NCdr p 

    doRecList : Val ctx (TList a) -> Val ctx x -> Val ctx (a :=> (TList a) :=> x :=> x) -> Val ctx x
    doRecList VNil b s = b
    doRecList (VCons x xs) b s = doApply (doApply (doApply s x) xs)
                                         (doRecList xs b s)
    doRecList (VNeutral xs) b s = VNeutral $ NRecList xs b s 

    public export
    eval : Env ctx' ctx -> Expr ctx a -> Val ctx' a
    eval env (Var x) = lookup x env 
    eval env (Lam f) = VClosure env f
    eval env (f :@ x) = doApply (eval env f) (eval env x)
    eval env Zero = VZero
    eval env (Add1 n) = VAdd1 $ eval env n
    eval env (The _ e) = eval env e
    eval env (Rec n b s) = doRec (eval env n) (eval env b) (eval env s)

    eval env (Cons a b) = VPair (eval env a) (eval env b)
    eval env (Car p) = doCar (eval env p)
    eval env (Cdr p) = doCdr (eval env p)

    eval env LNil = VNil
    eval env (LCons x xs) = VCons (eval env x) (eval env xs)

    eval env (RecList xs b s) = doRecList (eval env xs) (eval env b) (eval env s)
    
    eval env (Quote s) = VAtom s


infix 0 :<=
data Contains : Context -> Context -> Type where
    Refl : ctx `Contains` ctx
    Weak : ctx `Contains` ctx' -> (a :: ctx) `Contains` ctx'
    Lift : ctx `Contains` ctx' -> (a :: ctx) `Contains` (a :: ctx')

mutual
    liftDeBruijn : ctx `Contains` ctx' -> DeBruijn ctx' a -> DeBruijn ctx a
    liftDeBruijn Refl x = x
    liftDeBruijn (Weak x) k = S $ liftDeBruijn x k
    liftDeBruijn (Lift x) Z = Z
    liftDeBruijn (Lift x) (S k) = S $ liftDeBruijn x k

    liftVal : ctx `Contains` ctx' -> Val ctx' a -> Val ctx a
    liftVal _ VZero = VZero
    liftVal x (VAdd1 n) = VAdd1 $ liftVal x n
    liftVal Refl v = v
    liftVal x (VClosure env f) = VClosure (liftEnv x env) f
    liftVal x (VNeutral n) = VNeutral $ liftNeutral x n
    liftVal x (VPair a b) = VPair (liftVal x a) (liftVal x b)
    liftVal x VNil = VNil
    liftVal x (VCons a as) = VCons (liftVal x a) (liftVal x as)
    liftVal x v@(VAtom _) = liftVal x v

    liftEnv : ctx `Contains` ctx' -> Env ctx' c -> Env ctx c
    liftEnv _ Nil = Nil
    liftEnv Refl e = e
    liftEnv x (h :: r) = liftVal x h :: liftEnv x r

    liftNeutral : ctx `Contains` ctx' -> Neutral ctx' a -> Neutral ctx a
    liftNeutral x (NVar i) = NVar $ liftDeBruijn x i
    liftNeutral x (NApp f a) = NApp (liftNeutral x f) (liftVal x a)
    liftNeutral x (NRec n b s) = NRec (liftNeutral x n) (liftVal x b) (liftVal x s)
    liftNeutral x (NCar p) = NCar $ liftNeutral x p
    liftNeutral x (NCdr p) = NCdr $ liftNeutral x p
    liftNeutral x (NRecList xs b s) = NRecList (liftNeutral x xs) (liftVal x b) (liftVal x s)

mutual
    readback : Val ctx a -> Expr ctx a
    readback (VNeutral w) = nereadback w
    readback v@(VClosure _ _) = Lam $ readback $ doApply (liftVal (Weak Refl) v) $ VNeutral (NVar Z)
    readback VZero = Zero
    readback (VAdd1 n) = Add1 $ readback n
    readback p@(VPair a b) = Cons (readback a) (readback b)
    readback VNil = LNil
    readback (VCons x xs) = LCons (readback x) (readback xs)
    readback (VAtom s) = Quote s

    nereadback : Neutral ctx a -> Expr ctx a
    nereadback (NVar x) = Var x
    nereadback (NApp f x) = (nereadback f) :@ (readback x)
    nereadback (NRec n b s) = Rec (nereadback n) (readback b) (readback s)
    nereadback (NCar p) = Car $ nereadback p
    nereadback (NCdr p) = Cdr $ nereadback p
    nereadback (NRecList xs b s) = RecList (nereadback xs) (readback b) (readback s)


ide : (c : Context) -> Env c c
ide Nil = Nil
ide (a :: c) = (VNeutral $ NVar Z) :: (liftEnv (Weak Refl) (ide c))

public export
normal : {ctx : Context} -> Expr ctx a -> Expr ctx a
normal {ctx} t = readback (eval (ide ctx) t)
