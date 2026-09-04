#!/usr/bin/env python3
"""Generate programs that USE what they define, for checking rather than
parsing.

The parser's generator draws names at random, so almost every statement it
produces earns 'undefined variable' or 'unknown type' and the checker never
reaches inference, struct instantiation, op= dispatch or the graph-element
discipline. This one carries a context: names it has bound, structs it has
defined with their arities, aliases it has declared. Later statements draw
from it.

Programs are meant to be PLAUSIBLE, not correct. Roughly half of what comes
out has type errors, which is what the checker is mostly for: deciding which
complaint a program earns.

  gen_check.py N [SEED]   ->  N programs on stdout, '%%' between them
"""
import random
import sys

BUILTIN = ["Int", "Decimal", "String", "Fronce", "Edge", "UndirectedEdge", "Graph"]
SCALARS = {"Int": "7", "Decimal": "1.5", "String": '"s"', "Fronce": "#"}


class Ctx:
    def __init__(self, r):
        self.r = r
        self.vars = []        # (name, is_mut, kind) where kind is 'set'|'edge'|'other'
        self.structs = []     # (name, n_params, n_fields)
        self.aliases = []     # (name, n_params)
        self.n = 0

    def fresh(self, upper=False):
        self.n += 1
        return ("S" if upper else "v") + str(self.n)


def type_expr(c, depth=0):
    r = c.r
    choices = ["builtin"] * 4 + ["set", "sum"]
    if c.structs:
        choices.append("struct")
    if c.aliases:
        choices.append("alias")
    if depth > 1:
        choices = ["builtin"]
    k = r.choice(choices)
    if k == "builtin":
        return r.choice(BUILTIN)
    if k == "set":
        return "Set<" + type_expr(c, depth + 1) + ">"
    if k == "sum":
        return "Set<%s> + Set<%s>" % (type_expr(c, depth + 1), type_expr(c, depth + 1))
    if k == "struct":
        name, nparams, _ = r.choice(c.structs)
        if nparams == 0:
            return name
        # sometimes the wrong arity, so that path is exercised too
        n = nparams if r.random() < 0.8 else r.randint(0, 2)
        return name + "<" + ", ".join(type_expr(c, depth + 1) for _ in range(n)) + ">" if n else name
    name, nparams = r.choice(c.aliases)
    if nparams == 0:
        return name
    n = nparams if r.random() < 0.8 else r.randint(1, 2)
    return name + "<" + ", ".join(type_expr(c, depth + 1) for _ in range(n)) + ">"


def value(c, depth=0):
    r = c.r
    choices = ["lit", "lit", "set", "edge", "vertexset", "setop", "annedge"]
    if c.vars:
        choices += ["ref", "ref"]
    if c.structs:
        choices.append("init")
    if depth > 1:
        choices = ["lit"] + (["ref"] if c.vars else [])
    k = r.choice(choices)
    if k == "lit":
        return r.choice(["7", "1.5", '"s"', "#", "#3", "-2"])
    if k == "ref":
        return r.choice(c.vars)[0]
    if k == "setop":
        # '&' '^' '/' on values, which op= dispatch and the intersection and
        # difference rules need. Nothing else in this generator reaches them.
        op = r.choice("&^/")
        return (" %s " % op).join(
            "{" + value(c, depth + 1) + "}" for _ in range(r.randint(2, 3)))
    if k == "annedge":
        # an annotated edge, which side surgery must refuse as an op= RHS
        payload = r.choice(["7", "1.5", "#", '"s"'])
        return "{" + value(c, depth + 1) + "} -[" + payload + "]-> {" \
            + value(c, depth + 1) + "}"
    if k == "vertexset":
        return "{" + ", ".join(value(c, depth + 1) for _ in range(r.randint(1, 2))) + "}"
    if k == "set":
        n = r.randint(0, 2)
        return "{" + ", ".join(value(c, depth + 1) for _ in range(n)) + "}"
    if k == "edge":
        a = "{" + value(c, depth + 1) + "}"
        b = "{" + value(c, depth + 1) + "}"
        form = r.randint(0, 3)
        if form == 0:
            return f"{a} -> {b}"
        if form == 1:
            return f"{a} <-> {b}"
        if form == 2:
            payload = r.choice(["7", "1.5", "#", '"s"'])
            return a + " -[" + payload + "]-> " + b
        return f"{{{a} -> {b}}}"
    name, nparams, nfields = r.choice(c.structs)
    n = nfields if r.random() < 0.8 else r.randint(0, 3)
    args = ", ".join(value(c, depth + 1) for _ in range(n))
    inst = ""
    if nparams and r.random() < 0.4:
        parts = ["_" if r.random() < 0.5 else type_expr(c, 1) for _ in range(nparams)]
        inst = "<" + ", ".join(parts) + ">"
    return f"{name}{inst}({args})"


def statement(c):
    r = c.r
    k = r.random()
    if k < 0.16:
        name = c.fresh(True)
        nparams = r.choice([0, 0, 1, 2])
        ps = "<" + ", ".join("P%d" % i for i in range(nparams)) + ">" if nparams else ""
        nfields = r.randint(0, 3)
        # a parameter every field ignores is rejected, so mention them often
        fs = []
        for i in range(nfields):
            t = "P%d" % r.randrange(nparams) if nparams and r.random() < 0.6 \
                else type_expr(c)
            fs.append("f%d: %s" % (i, t))
        c.structs.append((name, nparams, nfields))
        return "struct %s%s { %s }" % (name, ps, ", ".join(fs))
    if k < 0.24:
        name = c.fresh(True)
        nparams = r.choice([0, 0, 1])
        ps = "<" + ", ".join("Q%d" % i for i in range(nparams)) + ">" if nparams else ""
        body = "Set<Q0>" if nparams else type_expr(c)
        c.aliases.append((name, nparams))
        return "type %s%s = %s" % (name, ps, body)
    if k < 0.36 and any(m for _, m, _ in c.vars):
        name = r.choice([v for v, m, _ in c.vars if m])
        return "%s %s= %s" % (name, r.choice("&^/"), value(c))
    name = c.fresh()
    is_mut = r.random() < 0.3
    ann = ""
    if r.random() < 0.5:
        t = type_expr(c)
        ann = ": " + (("mut " + t) if is_mut else t)
    else:
        is_mut = False
    c.vars.append((name, is_mut, "other"))
    return "let %s%s = %s" % (name, ann, value(c))


def program(r):
    c = Ctx(r)
    # A graph and a mut graph up front, so the element discipline is reached.
    # Seeded bindings of every shape op= dispatches on, so surgery and the
    # invariance rules are reachable. Random annotations almost never land on
    # a bare Edge or UndirectedEdge.
    lines = ["let g0: Graph = {{1} -> {2}}", "let m0: mut Graph = {}",
             "let e0: mut Edge = {1} -> {2}",
             "let u0: mut UndirectedEdge = {1} <-> {2}",
             "let s0: mut Set<Int> = {}"]
    c.vars += [("g0", False, "set"), ("m0", True, "set"), ("e0", True, "edge"),
               ("u0", True, "edge"), ("s0", True, "set")]
    for _ in range(r.randint(2, 7)):
        lines.append(statement(c))
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    count = int(sys.argv[1])
    r = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    for i in range(count):
        if i:
            print("%%")
        sys.stdout.write(program(r))
