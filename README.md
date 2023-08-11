# STLC-idris
An implementation of the simply typed lambda calculus (STLC) supporting primitive recursion on Nats using dependent types.

## What is this?
This is an implementation of a simply typed lambda calculus which also includes natural numbers and a construct for primitive recursion.

Usually, an implementation of an STLC requires type-checking. However, this implementation uses dependent types to bypass the need for a type checker by making ill-typed programs impossible to represent. In effect, this delegates the process of type-checking to the host language (in this case, Idris). 

This delegation has some notable side effects. In particular, even though the STLC does not technically support polymorphic types, this implementation inherits them "for free" from the host language. 

Technically, the Idris code only implements an evaluator and normalizer. Since writing programs directly as syntax trees is cumbersome and error prone, this repositor also contains scripts `stlc.py` and `run.sh` which allow for writing STLC programs using S-expression syntax. If `program.rkt` contains STLC code in this syntax, the command `./run.sh program.rkt` will translate that code into Idris code, run the Idris compiler, and output the result. 

## How does it work?
### Overview
STLC programs are represented as values of an `Expr` type, indexed by a context and a type which respectively represent the types of the variables in scope and the type of the expression itself. 

Expressions evaluate to a value of a `Val` type, which is also indexed by a context and a type. The type still represents the type of the STLC value, but the role of the context is a little subtler. Essentially, the context is used to keep track of "neutral variables", which comes into play during normalization.

Values are "normalized" or "read back" into expressions which are their normal form. In this STLC, normal forms are unique, and so can be thought of as the simplest possible program which can produce a given value. Thus, `(lambda (x) (add1 (add1 x)))` and `(lambda (x) (add1 ((lambda (y) y) (add1 x))))` both "do the same thing", but the former is clearly "simpler".
### The `Ty` type
The `Ty` type represents the types of STLC values. A `Ty` is either `TNat`, representing the type of natural numbers, or `a :=> b` for `a b : Ty`, representing a function from `a` to `b`.
### Contexts and De Bruijn indices
Variables are represented by their De Bruijn index, which is a non-negative integer representing the number of binders between the variables occurrence and its initial binding site.

A context is simply a list of types. The type of the variable with De Bruijn index `i` is given by the `i`th element of the context. A variable of type `a` is constructed by providing a De Bruijn index for the given context.
### The `Expr` type
The `Expr` type is indexed by a context and a `Ty`. These two indices allow for the type of the constructors of the `Expr` type to fully encode the typing rules of the STLC. Consider:
```idris
data Expr : Context -> Ty -> Type where
    Var : DeBruijn ctx a -> Expr ctx a
    Lam : Expr (a :: ctx) b -> Expr ctx (a :=> b)
    (:@) : Expr ctx (a :=> b) -> Expr ctx a -> Expr ctx b
    Zero : Expr ctx TNat
    Add1 : Expr ctx TNat -> Expr ctx TNat
    Rec : Expr ctx TNat -> Expr ctx a -> Expr ctx (TNat :=> a :=> a) -> Expr ctx a
    The : (a : Ty) -> Expr ctx a -> Expr ctx a
```
The type of the `Var` constructor ensures that one can't reference a variable which does not exist in the context. 

Similarly, the type of the `Lam` constructor can be read as the typing rule "if `f` has type `b` in a context with `x` a value of type `a`, then the the term `lambda x. f` has type `a :=> b`."
### The `Val` type
The `Val` type is defined by mutual recursion with the `Neutral` type and the `Env` type, which represent "neutral" STLC values and an evaluation environment.

A neutral value is a "stuck" computation; something that can not be evaluated further. Computation in this STLC only occurs during
 1. variable lookups
 2. applications of one term to another
 3. primitive recursion
so the `Neutral` type has a constructor corresponding to each case:
```idris
data Neutral : Context -> Ty -> Type where
    NVar : DeBruijn ctx a -> Neutral ctx a
    NApp : Neutral ctx (a :=> b) -> Val ctx a -> Neutral ctx b
    NRec : Neutral ctx TNat -> Val ctx a -> Val ctx (TNat :=> a :=> a) -> Neutral ctx a
```

The `Env` type is indexed on _two_ contexts: the first is the context on which the values in the environment are all indexed, while the second gives the actual mapping between variables and their types:
```idris
data Env : Context -> Context -> Type where
    Empty : Env ctx' Nil
    (:::) : Val ctx' a -> Env ctx' ctx -> Env ctx' (a :: ctx)
```

Finally, a `Val ctx a` is either neutral, a natural number, or a lambda abstraction. The last is represented as an expression bundled with an environment, giving:
```idris
data Val : Context -> Ty -> Type where
    VNeutral : Neutral ctx a -> Val ctx a
    VClosure : Env ctx' ctx -> Expr (a :: ctx) b -> Val ctx' (a :=> b)

    VZero : Val ctx TNat
    VAdd1 : Val ctx TNat -> Val ctx TNat
```
### Evaluation
Given an `Env ctx' ctx` and an `Expr ctx a`, we produce a `Val ctx' a` by the process of evaluation.
```idris
eval : Env ctx' ctx -> Expr ctx a -> Val ctx' a
```
Evaluating a variable corresponds to a lookup in the environment, which is guaranteed to succeed since variables can only be constructed via valid De Bruijn indices:
```idris
lookup : DeBruijn ctx a -> Env ctx' ctx -> Val ctx' a
lookup Stop (a ::: r) = a
lookup (Pop k) (a ::: r) = lookup k r

eval env (Var x) = lookup x env 
```
Evaluating a lambda abstraction just means creating the closure:
```idris
eval env (Lam f) = VClosure env f
```
Evaluating the application of `f` to `x` is done by evaluating the body of `f` in an environment extended with `x`:
```idris
doApply : Val ctx (a :=> b) -> Val ctx a -> Val ctx b
doApply (VClosure env f) x = eval (x ::: env) f
doApply (VNeutral f) x = VNeutral $ NApp f x

eval env (f :@ x) = doApply (eval env f) (eval env x)
```
We evaluate primitive recursion by calling the evaluator recursively:
```idris
doRec : Val ctx TNat -> Val ctx a -> Val ctx (TNat :=> a :=> a) -> Val ctx a
doRec VZero b s = b
doRec (VAdd1 n) b s = doApply (doApply s n)
                                (doRec n b s)
doRec (VNeutral n) b s = VNeutral $ NRec n b s

eval env (Rec n b s) = doRec (eval env n) (eval env b) (eval env s)
```
The remaining cases are straightforward:
```idris
eval env Zero = VZero
eval env (Add1 n) = VAdd1 $ eval env n
eval env (The _ e) = eval env e
```
### Normalization
In normalization, we want to take a `Val ctx a` and produce an `Expr ctx a`. Since a `Val` is either neutral or not, we split the normalization process into two functions:
```idris
readback : Val ctx a -> Expr ctx a

nereadback : Neutral ctx a -> Expr ctx a
```
The constructors of the `Neutral` type correspond directly to constructors of the `Expr` type, so normalizing them is fairly easy:
```idris
readback (VNeutral w) = nereadback w

nereadback (NVar x) = Var x
nereadback (NApp f x) = (nereadback f) :@ (readback x)
nereadback (NRec n b s) = Rec (nereadback n) (readback b) (readback s)
```
Similarly, reading back `VZero` and `VAdd1 n` is easy, as they two correspond directly to syntax:
```idris
readback VZero = Zero
readback (VAdd1 n) = Add1 $ readback n
```
Normalizing a lambda abstraction is trickier, though, since the body of a lambda term might still contain unrealized computation that should be simplified. We can achieve this by applying a function value to a neutral variable, normalizing the result, and then wrapping that in `Lam`.

However, to apply a `Val ctx (a :=> b)`, we need to extend `ctx` with a value of type `a`. To do so, we define a relation `:<=` on contexts, whereby `ctx :<= ctx'` if and only if `ctx` can be obtained from `ctx'` by adding more types onto the front. The intuition here is that if `v` has type `a` in some context `C`, then adding more things into the context shouldn't affect the type of `v`.

In code, the relation `:<=` is defined as a data type:
```idris
data (:<=) : Context -> Context -> Type where
    Refl : ctx :<= ctx
    Weak : ctx :<= ctx' -> (a :: ctx) :<= ctx'
    Lift : ctx :<= ctx' -> (a :: ctx) :<= (a :: ctx')
```

Then, if `ctx :<= ctx'` and we have `v` a `Val ctx' a`, we should also be able to obtain a `Val ctx a`. Again, `ctx :<= ctx'` means `ctx` contains "more stuff" than `ctx'`, which shouldn't affect the type of `v`. So, we define
```idris
weakenVal : ctx :<= ctx' -> Val ctx' a -> Val ctx a
```

In fact, since the `Val` type depends also on the `Env`, `Neutral`, and `DeBruijn` types, which all depend on a context, we also need to define
```idris
weakenDeBruijn : ctx :<= ctx' -> DeBruijn ctx' a -> DeBruijn ctx a
weakenEnv : ctx :<= ctx' -> Env ctx' c -> Env ctx c
weakenNeutral : ctx :<= ctx' -> Neutral ctx' a -> Neutral ctx a
```

Finally, we can normalize a function value as follows:
```idris
readback v@(VClosure _ _) = Lam $ readback $ doApply (weakenVal (Weak Refl) v) $ VNeutral (NVar Stop)
```

