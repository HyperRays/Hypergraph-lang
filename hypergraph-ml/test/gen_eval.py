#!/usr/bin/env python3
"""Generate programs that typecheck, so the evaluator is actually reached.

gen_check.py aims at the checker and most of what it emits has type errors, so
only 16 programs in 250 ever got drawn. This one stays well-typed by
construction and aims instead at the decisions evaluation makes: identity,
duplicate elimination, fronce minting, set operations, op= dispatch, the
nominal graph discipline, and the shapes that end up as rows and columns.

The edge cases it deliberately reaches:

  self-loops          '{1} <-> {1}', whose two halves are the same edge
  duplicates          the same edge written twice, which collapses
  unordered sides     '{1,2} -> {3}' equals '{2,1} -> {3}'
  orientation         '{1} <-> {2}' and '{2} <-> {1}' are two elements
  minted fronce       '#' twice makes two distinct edges
  pinned fronce       '#N', unique per program, matched in '^' and '/'
  named graphs        as set elements, compared by name and never expanded
  empty graphs        which draw nothing, alone and beside a non-empty one
  struct vertices     compared positionally
  integral decimals   '2.0', which must not read as the integer 2
  twin graphs         two names holding the SAME edges, which stay two
                      elements because graph identity is the name
  twin empties        two empty graphs, which are NOT graph-valued and so
                      compare structurally and collapse to one

  gen_eval.py N [SEED]   ->  N programs on stdout, '%%' between them
"""
import random
import sys

VERTS = ["1", "2", "3", '"a"', '"b"', "1.5", "2.0", "0.0",
         '"日本橋"', '"Zürich"']


class Ctx:
    def __init__(self, r):
        self.r = r
        self.graphs = []   # non-mut graph names, usable as elements
        self.muts = []     # mut Graph names
        self.pins = []     # pinned fronce indices introduced so far
        self.twins = None  # a pair of names holding identical edges
        self.n = 0

    def fresh(self, p="v"):
        self.n += 1
        return p + str(self.n)


def vertex(c):
    r = c.r
    if r.random() < 0.15:
        return "City(%s, %d)" % (r.choice(['"x"', '"y"', '"日本"']), r.randint(0, 9))
    return r.choice(VERTS)


def side(c):
    """A vertex set. More than one vertex is what makes side order matter.

    A named graph may stand here, and only here: as a top-level element it
    becomes a GROUP rather than a row, so the rule that a graph-valued vertex
    interns by its NAME is reached from a vertex position and nowhere else.
    """
    r = c.r
    n = 1 if r.random() < 0.7 else 2
    parts = [vertex(c) for _ in range(n)]
    if c.graphs and r.random() < 0.15:
        parts[0] = r.choice(c.graphs)
    return "{" + ", ".join(parts) + "}"


def payload(c, minted_ok=True):
    r = c.r
    k = r.random()
    if k < 0.3 and minted_ok:
        return "#"                       # mints, so two are distinct
    if k < 0.5:
        idx = r.randint(0, 20)
        if idx in c.pins:
            return None                  # a pin may be written only once
        c.pins.append(idx)
        return "#%d" % idx
    return r.choice(["7", "1.5", '"p"'])


def edge(c, minted_ok=True, plain=False):
    r = c.r
    a, b = side(c), side(c)
    if r.random() < 0.12:
        b = a                            # self-loop
    k = r.random()
    if plain or k < 0.45:
        return "%s -> %s" % (a, b)
    if k < 0.7:
        return "%s <-> %s" % (a, b)
    p = payload(c, minted_ok)
    if p is None:
        return "%s -> %s" % (a, b)
    return "%s -[%s]-> %s" % (a, p, b) if r.random() < 0.6 \
        else "%s <-[%s]-> %s" % (a, p, b)


def graph_literal(c, minted_ok=True, plain=False):
    r = c.r
    n = r.randint(0, 3)
    parts = [edge(c, minted_ok, plain) for _ in range(n)]
    if parts and r.random() < 0.2:
        parts.append(parts[0])           # a duplicate, which collapses
    return "{" + ", ".join(parts) + "}"


def statement(c):
    r = c.r
    k = r.random()

    # op= on a mut graph. '^' and '/' are matching positions, so nothing
    # under them may mint.
    if k < 0.2 and c.muts:
        name = r.choice(c.muts)
        op = r.choice(["&=", "^=", "/="])
        rhs = graph_literal(c, minted_ok=(op == "&="), plain=True)
        return "%s %s %s" % (name, op, rhs)

    if k < 0.3:
        name = c.fresh("m")
        body = graph_literal(c, plain=True)
        c.muts.append(name)
        return "let %s: mut Graph = %s" % (name, body)

    # A set operation between two named graphs.
    if k < 0.42 and len(c.graphs) >= 2:
        a, b = r.sample(c.graphs, 2)
        name = c.fresh()
        c.graphs.append(name)
        return "let %s = %s %s %s" % (name, a, r.choice("&^/"), b)

    # A bare undirected edge, then that edge as an OPERAND. as_elems only
    # runs in operand position, so nothing else reaches the rule that a
    # self-loop's two halves are the same edge and collapse to one. The mut
    # Set<Edge> binding is the coercion path, where the checker's declaration
    # decides whether the value is stored realised.
    if k < 0.4 and c.graphs:
        a, b = side(c), side(c)
        if r.random() < 0.5:
            b = a                        # self-loop: two halves, one edge
        u, z = c.fresh("u"), c.fresh("z")
        if r.random() < 0.5:
            c.graphs.append(z)
            return "let %s: mut Set<Edge> = %s <-> %s\nlet %s = %s" % (
                u, a, b, z, u)
        other = r.choice(c.graphs)
        c.graphs.append(z)
        return "let %s = %s <-> %s\nlet %s = %s %s %s" % (
            u, a, b, z, u, r.choice("&^/"), other)

    # Two names holding the same edges. Graph identity is the NAME, so a set
    # containing both keeps two elements; comparing structurally would merge
    # them, and nothing else this generator emits would notice.
    if k < 0.48 and c.twins is None:
        a, b = c.fresh("t"), c.fresh("t")
        body = graph_literal(c, minted_ok=False)
        c.twins = (a, b)
        c.graphs += [a, b]  # after the body, so neither can name itself
        return "let %s = %s\nlet %s = %s" % (a, body, b, body)

    # Named graphs as elements: identity is the name, never the structure.
    if k < 0.56 and c.graphs:
        name = c.fresh("atlas")
        members = r.sample(c.graphs, min(len(c.graphs), r.randint(1, 2)))
        extra = [edge(c)] if r.random() < 0.5 else []
        c.graphs.append(name)  # after the members are chosen
        return "let %s = {%s}" % (name, ", ".join(members + extra))

    name = c.fresh("g")
    body = graph_literal(c)      # before binding, so it cannot name itself
    c.graphs.append(name)
    return "let %s = %s" % (name, body)


def program(r):
    c = Ctx(r)
    lines = ["struct City { name: String, pop: Int }"]
    # An empty graph up front: it draws nothing on its own, and it must still
    # count as a member when it sits beside one that does.
    if r.random() < 0.4:
        # Two of them: an empty set is NOT graph-valued, so these compare
        # structurally and collapse, where two non-empty graphs would not.
        lines += ["let empty = {}", "let empty2 = {}"]
        c.graphs += ["empty", "empty2"]
    for _ in range(r.randint(2, 6)):
        lines.append(statement(c))
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    count = int(sys.argv[1])
    r = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    for i in range(count):
        if i:
            print("%%")
        sys.stdout.write(program(r))
