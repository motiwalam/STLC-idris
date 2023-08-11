from numbers import Number
import sys
from sexpdata import Symbol, parse as parse_sexpr
from dataclasses import dataclass
from functools import reduce as foldl

foldr = lambda f, xs, i: foldl(lambda a, b: f(b, a), reversed(xs), i)

class Expr: pass

@dataclass
class Var(Expr):
    x: str

@dataclass
class Lam(Expr):
    x: str
    b: Expr

@dataclass
class App(Expr):
    f: Expr
    x: Expr

@dataclass
class Rec(Expr):
    n: Expr
    b: Expr
    s: Expr

@dataclass
class Zero(Expr): pass

@dataclass
class Add1(Expr):
    n: Expr

@dataclass
class Nat(Expr): pass

@dataclass
class Arr(Expr):
    a: Expr
    b: Expr

@dataclass
class The(Expr):
    a: Expr
    e: Expr

@dataclass
class Def:
    ty: Expr
    body: Expr

def nat_to_expr(y):
    return foldl(lambda acc, x: x(acc), [Add1] * y, Zero())

Env = dict[str, Def]

def claim(env: Env, name: str, ty: Expr) -> Env:
    d = Def(ty, None)
    if name in env:
        d.body = env[name].body
    return env | {name: d}

def define(env: Env, name: str, body: Expr) -> Env:
    d = Def(None, body)
    if name in env:
        d.ty = env[name].ty
    return env | {name: d}

def de_bruijn(i):
    def index(i):
        if i == 0:
            return 'Stop'
        
        return f'Pop ({index(i-1)})'
    
    return f'Var ({index(i)})'

def to_idris(expr: Expr) -> str:
    def helper(ns: list[str], expr):
        match expr:
            case Var(x):
                if x in ns:
                    i = ns.index(x)
                    return de_bruijn(i)
                return x
            case Lam(x, f):
                return f'Lam ({helper([x, *ns], f)})'
            case App(f, x):
                return f'({helper(ns, f)}) :@ ({helper(ns, x)})'
            case Rec(n, b, s):
                return f'Rec ({helper(ns, n)}) ({helper(ns, b)}) ({helper(ns, s)})'
            case Zero():
                return 'Zero'
            case Add1(n):
                return f'Add1 ({helper(ns, n)})'
            case Nat():
                return 'TNat'
            case Arr(a,b):
                return f'({helper(ns, a)}) :=> ({helper(ns, b)})'
            case The(a, e):
                return f'The ({helper(ns, a)}) ({helper(ns, e)})'

    return helper([], expr)

def env_to_idris(env: Env) -> str:
    p = ""
    for name, d in env.items():
        p += f'{name} : Expr ctx $ {to_idris(d.ty) if d.ty else f"?{name}_t"}\n'
        if d.body:
            p += f'{name} = {to_idris(d.body)}\n'
        p += '\n\n'
    return p

def do_term(term) -> Expr:
    match term:        
        case [Symbol('lambda'), symbols, body]:
            return foldr(
                lambda x, acc: Lam(str(x), acc),
                symbols,
                do_term(body)
            )

        case [Symbol('rec'), target, base, step]:
            return Rec(
                do_term(target),
                do_term(base),
                do_term(step)
            )

        case [Symbol('add1'), n]:
            return Add1(do_term(n))

        case Symbol('zero'):
            return Zero()
        
        case [Symbol('the'), a, e]:
            return The(do_term(a), do_term(e))
        
        case Symbol('Nat'):
            return Nat()
        
        case [Symbol('->'), *r, t1, t2]:
            return foldr(
                lambda x, acc: Arr(do_term(x), acc), 
                r, 
                Arr(do_term(t1), do_term(t2)))

        case [rator, x, *rands]:
            return foldl(lambda acc, x: App(acc, do_term(x)), rands, App(do_term(rator), do_term(x)))

        case Symbol(x):
            return Var(x)

        case x:
            if isinstance(x, Number):
                if (y := int(x)) == x:
                    if y < 0:
                        f'Negative natural: {y}'
                    
                    return nat_to_expr(y)
                
                else:
                    f"Invalid natural: {x}"

            else:
                f'Unrecognized form: {x}'

def process(program):
    env = {}
    results = []
    for term in program:
        match term:
            case [Symbol('claim'), Symbol(x), val]:
                t = do_term(val)
                env = claim(env, x, t)

            case [Symbol('define'), Symbol(x), val]:
                t = do_term(val)
                env = define(env, x, t)
            
            case x:
                results.append(do_term(x))

    return env, results

def main(fn,outfile="Main.idr"):
    with open(fn) as f:
        p = parse_sexpr(f.read())
    
    env,results = process(p)
    
    result_i = '\n\n'.join(
        f'r{i} : Expr ?ctx{i} ?a{i}\nr{i} = normal $ {to_idris(r)}'
        for i, r in enumerate(results) 
    )

    header = f"module {outfile.removesuffix('.idr')}\n\nimport STLC\n\n"
    body = env_to_idris(env) + result_i
    with open(outfile, 'w') as f:
        f.write(header + body)

    print('\n'.join(f'show_expr r{i}' for i in range(len(results))))


if __name__ == "__main__":
    raise SystemExit(main(*sys.argv[1:]))