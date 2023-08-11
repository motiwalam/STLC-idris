from numbers import Number
import sys
from sexpdata import Symbol, Brackets, Quoted, parse as parse_sexpr
from dataclasses import dataclass
from functools import reduce as foldl

foldr = lambda f, xs, i: foldl(lambda a, b: f(b, a), reversed(xs), i)

class ParseError(Exception): pass

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
class Cons(Expr):
    car : Expr
    cdr : Expr

@dataclass
class Car(Expr):
    p: Expr

@dataclass
class Cdr(Expr):
    p: Expr

@dataclass 
class Nil(Expr): pass

@dataclass
class LCons(Expr):
    x: Expr
    xs: Expr

@dataclass
class RecList(Expr): 
    xs: Expr
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
class Atom(Expr): pass

@dataclass
class Quote(Expr):
    s: str

@dataclass
class Arr(Expr):
    a: Expr
    b: Expr

@dataclass 
class Pair(Expr):
    car_t: Expr
    cdr_t : Expr

@dataclass
class List(Expr):
    a: Expr

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
            return 'Z'
        
        return f'S ({index(i-1)})'
    
    return f'Var ({index(i)})'

def symb_to_idris(x: str) -> str:
    return (
        x.replace('?', 'q')
         .replace('-', '_')
         .replace('+', 'plus')
         .replace('*', 'times')
         .replace('/', 'slash')
         .replace('&', 'amp')
         .replace('%', 'percent')
         .replace('$', 'dollar')
         .replace('@', 'at')
         .replace('!', 'ex')
         .replace('#', 'hash')
         .replace('<', 'lt')
         .replace('>', 'gt')
         .replace('=', 'eq')
    )

def to_idris(expr: Expr) -> str:
    def helper(ns: list[str], expr):
        match expr:
            case Var(x):
                if x in ns:
                    i = ns.index(x)
                    return de_bruijn(i)
                return symb_to_idris(x)
            
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
            case Cons(a,b):
                return f'Cons ({helper(ns, a)}) ({helper(ns, b)})'
            case Car(p):
                return f'Car ({helper(ns, p)})'
            case Cdr(p):
                return f'Cdr ({helper(ns, p)})'
            case Nil():
                return 'LNil'
            case LCons(x,xs):
                return f'LCons ({helper(ns, x)}) ({helper(ns, xs)})'
            case RecList(xs,b,s):
                return f'RecList ({helper(ns, xs)}) ({helper(ns, b)}) ({helper(ns, s)})'
            case Nat():
                return 'TNat'
            case Arr(a,b):
                return f'({helper(ns, a)}) :=> ({helper(ns, b)})'
            case Pair(at,dt):
                return f'TPair ({helper(ns, at)}) ({helper(ns, dt)})'
            case List(a):
                return f'TList ({helper(ns, a)})'
            case The(a, e):
                return f'The ({helper(ns, a)}) ({helper(ns, e)})'
            case Atom():
                return 'Atom'
            case Quote(s):
                return f'Quote "{s}"'

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
        case [Symbol('lambda'), [*symbols, x1], body]:
            return foldr(
                lambda x, acc: Lam(str(x), acc),
                symbols,
                Lam(str(x1), do_term(body))
            )

        case [Symbol('rec-nat'), target, base, step]:
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
        
        case [Symbol('cons'), a, b]:
            return Cons(do_term(a), do_term(b))
        
        case [Symbol(','), *r, a, b]:
            return foldr(
                lambda x, acc: Cons(do_term(x), acc),
                r,
                Cons(do_term(a), do_term(b))
            )
        
        case [Symbol('car'), p]:
            return Car(do_term(p))
        
        case [Symbol('cdr'), p]:
            return Cdr(do_term(p))
        
        case Symbol('nil'):
            return Nil()
        
        case [Symbol('List'), a]:
            return List(do_term(a))
        
        case [Symbol('::'), x, xs]:
            return LCons(do_term(x), do_term(xs))
        
        case [Symbol('rec-list'), xs, b, s]:
            return RecList(do_term(xs), do_term(b), do_term(s))
        
        case Brackets(lst):
            return foldr(
                lambda x, acc: LCons(do_term(x), acc),
                lst,
                Nil()
            )
        
        case Symbol('Nat'):
            return Nat()
        
        case [Symbol('->'), *r, t1, t2]:
            return foldr(
                lambda x, acc: Arr(do_term(x), acc), 
                r, 
                Arr(do_term(t1), do_term(t2)))
        
        case Symbol('Atom'):
            return Atom()
        
        case Quoted(Symbol(x)):
            return Quote(x)
        
        case Quoted(x):
            raise ParseError(f'invalid atom {x}')

        case [rator, x, *rands]:
            return foldl(lambda acc, x: App(acc, do_term(x)), rands, App(do_term(rator), do_term(x)))

        case Symbol(x):
            return Var(x)

        case x:
            if isinstance(x, Number):
                if (y := int(x)) == x:
                    if y < 0:
                        raise ParseError(f'Negative natural: {y}')
                    
                    return nat_to_expr(y)
                
                else:
                    raise ParseError(f"Invalid natural: {x}")

            else:
                raise ParseError(f'Unrecognized form: {x}')

def process(program):
    env = {}
    results = []
    for term in program:
        match term:
            case [Symbol('claim'), Symbol(x), val]:
                t = do_term(val)
                env = claim(env, symb_to_idris(x), t)

            case [Symbol('define'), Symbol(x), val]:
                t = do_term(val)
                env = define(env, symb_to_idris(x), t)
            
            case x:
                results.append(do_term(x))

    return env, results

def main(fn,outfile="Main.idr"):
    with open(fn) as f:
        p = parse_sexpr(f.read(), nil='', true='')
    
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