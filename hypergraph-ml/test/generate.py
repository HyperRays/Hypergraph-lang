#!/usr/bin/env python3
"""Generate random programs in the language, to compare two parsers on inputs
neither author thought to write.

A hand-written corpus covers what its author remembered. This walks the
grammar, so it reaches combinations nobody wrote down: an annotated edge whose
payload is a struct initialiser containing a set operation, a type whose
argument is a sum of juxtapositions, a set spanning lines with a comment in the
middle of it.

Every program it emits is meant to PARSE. Whether it typechecks is a separate
judgment with a separate oracle.

Each production records that it fired, so coverage is measured rather than
claimed. 'Edge(...)' is why that matters: the generator built struct
initialisers from random capitalised names, the alphabet could not spell
'Edge', and a bug in the constructor form survived 1300 programs unseen.

  generate.py N [SEED]        N programs on stdout, '%%' between them
  generate.py --features      every feature name, one per line
"""
import random
import sys

KEYWORDS = {"let", "struct", "type"}

# Every production this generator can emit, and how often it did.
FEATURES = {}


def hit(name):
    FEATURES[name] = FEATURES.get(name, 0) + 1


ALL_FEATURES = [
    # statements
    "stmt:let", "stmt:let_annotated", "stmt:ext", "stmt:struct", "stmt:typedef",
    "struct:params", "struct:no_params", "struct:no_fields",
    "struct:trailing_comma", "struct:multiline",
    "typedef:params", "typedef:no_params",
    # types
    "type:sum", "type:single", "type:mut", "type:juxtaposition",
    "tatom:name", "tatom:args", "tatom:args_multi", "tatom:group",
    # values
    "value:int", "value:int_negative", "value:int_underscore",
    "value:decimal", "value:decimal_negative",
    "value:string_double", "value:string_single", "value:string_escape",
    "value:string_unicode", "value:fronce_mint", "value:fronce_pinned",
    "value:ref", "value:paren_nonset",
    # sets
    "set:empty", "set:elems", "set:trailing_comma", "set:multiline", "set:nested",
    "setop:union", "setop:inter", "setop:diff", "setop:chain3", "setop:paren",
    # edges
    "edge:arrow_r", "edge:arrow_l", "edge:arrow_lr",
    "edge:ann_r", "edge:ann_l", "edge:ann_lr",
    "edge:ctor", "edge:ctor_payload", "edge:ctor_notset", "edge:paren",
    # struct init
    "init:plain", "init:targs", "init:hole", "init:targs_sum",
    "init:no_args", "init:trailing_comma",
    "opeq:union", "opeq:inter", "opeq:diff",
    "set:newline_before_comma", "struct:newline_around_comma",
    # trivia
    "trivia:comment_line", "trivia:comment_trailing", "trivia:blank_line",
    "trivia:comment_in_set",
]


def name(r, upper=False):
    while True:
        n = r.choice("ABCDEFGHIJ" if upper else "abcdefghij")
        n += "".join(r.choice("abcxyz012_") for _ in range(r.randint(0, 3)))
        if n not in KEYWORDS:
            return n


def string(r):
    """Both quote kinds, every escape the grammar admits, and non-ASCII text."""
    escapes = ["\\n", "\\t", "\\r", "\\b", "\\f", "\\\\", "\\/", "\\`"]
    single = r.random() < 0.3
    delim, other = ("'", '"') if single else ('"', "'")
    hit("value:string_single" if single else "value:string_double")
    parts = []
    for _ in range(r.randint(0, 4)):
        c = r.random()
        if c < 0.3:
            parts.append(r.choice(escapes))
            hit("value:string_escape")
        elif c < 0.45:
            parts.append("\\" + delim)
            hit("value:string_escape")
        elif c < 0.6:
            parts.append(r.choice(["ü", "日", "é"]))
            hit("value:string_unicode")
        else:
            parts.append(r.choice(["a", "Z", "9", " ", other]))
    return delim + "".join(parts) + delim


def number(r):
    if r.random() < 0.3:
        sign = "-" if r.random() < 0.4 else ""
        hit("value:decimal_negative" if sign else "value:decimal")
        return f"{sign}{r.randint(0, 999)}.{r.randint(0, 99)}"
    sign = "-" if r.random() < 0.3 else ""
    digits = str(r.randint(0, 9999))
    if r.random() < 0.3 and len(digits) > 1:
        cut = r.randint(1, len(digits) - 1)
        digits = digits[:cut] + "_" + digits[cut:]
        hit("value:int_underscore")
    hit("value:int_negative" if sign else "value:int")
    return sign + digits


def tsum(r, d=0):
    n = r.randint(1, 2)
    hit("type:sum" if n > 1 else "type:single")
    return " + ".join(tapp(r, d) for _ in range(n))


def tapp(r, d):
    parts = []
    if r.random() < 0.2:
        parts.append("mut")
        hit("type:mut")
    parts.append(tatom(r, d))
    # 'type_app = type_atom+', so a bare juxtaposition is legal syntax even
    # where the checker will go on to reject it.
    if r.random() < 0.1:
        parts.append(tatom(r, d))
        hit("type:juxtaposition")
    return " ".join(parts)


def tatom(r, d):
    c = r.random()
    if d < 2 and c < 0.3:
        n = r.randint(1, 2)
        hit("tatom:args_multi" if n > 1 else "tatom:args")
        return f"{name(r, True)}<{', '.join(tsum(r, d + 1) for _ in range(n))}>"
    if d < 2 and c < 0.4:
        hit("tatom:group")
        return f"({tsum(r, d + 1)})"
    hit("tatom:name")
    return name(r, True)


def sexpr(r, d):
    """A set expression: one atom, or a chain of ONE operator kind."""
    n = r.randint(1, 3)
    atoms = [satom(r, d) for _ in range(n)]
    if n == 1:
        return atoms[0]
    if n >= 3:
        hit("setop:chain3")
    op = r.choice("&^/")
    hit({"&": "setop:union", "^": "setop:inter", "/": "setop:diff"}[op])
    return f" {op} ".join(atoms)


def satom(r, d):
    c = r.random()
    if d < 3 and c < 0.55:
        n = r.randint(0, 3)
        if n == 0:
            hit("set:empty")
            return "{}"
        inner = [value(r, d + 1) for _ in range(n)]
        hit("set:elems")
        if any(x.startswith("{") for x in inner):
            hit("set:nested")
        sep = ", "
        c2 = r.random()
        if c2 < 0.15:
            sep = ",\n  "
            hit("set:multiline")
        elif c2 < 0.25:
            sep = "\n  , "
            hit("set:newline_before_comma")
            hit("set:multiline")
        elif c2 < 0.32:
            sep = ",  // inside\n  "
            hit("trivia:comment_in_set")
            hit("set:multiline")
        trail = ""
        if r.random() < 0.2:
            trail = ","
            hit("set:trailing_comma")
        return "{" + sep.join(inner) + trail + "}"
    if d < 3 and c < 0.65:
        # A parenthesised set operand holds a set expression, not any value:
        # '(3339) / x' is refused where '(a & b) / x' is fine.
        hit("setop:paren")
        return f"({sexpr(r, d + 1)})"
    hit("value:ref")
    return name(r)


def value(r, d=0):
    c = r.random()
    if d >= 3:
        return r.choice([number(r), string(r), name(r), "#", "{}"])
    if c < 0.26:
        return edge(r, d)
    if c < 0.34:
        return number(r)
    if c < 0.41:
        return string(r)
    if c < 0.48:
        if r.random() < 0.5:
            hit("value:fronce_pinned")
            return "#" + str(r.randint(0, 99))
        hit("value:fronce_mint")
        return "#"
    if c < 0.54:
        # 'rhs = ... | "(" rhs ")"', so a parenthesised non-set value is legal
        # on its own even though it cannot be a set operand.
        hit("value:paren_nonset")
        return f"({number(r) if r.random() < 0.5 else string(r)})"
    if c < 0.68:
        return init(r, d)
    return sexpr(r, d)


def init(r, d):
    """A struct initialiser, or the Edge constructor when it spells one."""
    as_edge = r.random() < 0.18
    nm = "Edge" if as_edge else name(r, True)
    if as_edge:
        # Both shapes on purpose: set sides make it an arrow, anything else
        # makes it a struct initialiser that happens to be named Edge.
        if r.random() < 0.7:
            a, b = sexpr(r, d + 1), sexpr(r, d + 1)
            if r.random() < 0.4:
                hit("edge:ctor_payload")
                return f"Edge({a}, {b}, {value(r, d + 2)})"
            hit("edge:ctor")
            return f"Edge({a}, {b})"
        hit("edge:ctor_notset")
        return f"Edge({number(r)}, {sexpr(r, d + 1)})"
    inst = ""
    if r.random() < 0.3:
        parts = []
        for _ in range(r.randint(1, 2)):
            if r.random() < 0.4:
                parts.append("_")
                hit("init:hole")
            else:
                parts.append(tsum(r, 1))
                hit("init:targs_sum")
        inst = "<" + ", ".join(parts) + ">"
        hit("init:targs")
    n = r.randint(0, 3)
    if n == 0:
        hit("init:no_args")
        return f"{nm}{inst}()"
    args = [value(r, d + 1) for _ in range(n)]
    trail = ""
    if r.random() < 0.15:
        trail = ","
        hit("init:trailing_comma")
    hit("init:plain")
    return f"{nm}{inst}({', '.join(args)}{trail})"


def edge(r, d):
    a, b = sexpr(r, d + 1), sexpr(r, d + 1)
    form = r.randint(0, 5)
    if form == 0:
        hit("edge:arrow_r")
        out = f"{a} -> {b}"
    elif form == 1:
        hit("edge:arrow_l")
        out = f"{a} <- {b}"
    elif form == 2:
        hit("edge:arrow_lr")
        out = f"{a} <-> {b}"
    else:
        p = value(r, d + 2)
        if form == 3:
            hit("edge:ann_r")
            out = f"{a} -[{p}]-> {b}"
        elif form == 4:
            hit("edge:ann_l")
            out = f"{a} <-[{p}]- {b}"
        else:
            hit("edge:ann_lr")
            out = f"{a} <-[{p}]-> {b}"
    if r.random() < 0.12:
        hit("edge:paren")
        return f"({out})"
    return out


def stmt(r):
    c = r.random()
    if c < 0.5:
        if r.random() < 0.4:
            hit("stmt:let_annotated")
            return f"let {name(r)}: {tsum(r)} = {value(r)}"
        hit("stmt:let")
        return f"let {name(r)} = {value(r)}"
    if c < 0.66:
        hit("stmt:ext")
        rhs = edge(r, 0) if r.random() < 0.4 else sexpr(r, 0)
        op = r.choice(["&=", "^=", "/="])
        hit({"&=": "opeq:union", "^=": "opeq:inter", "/=": "opeq:diff"}[op])
        return f"{name(r)} {op} {rhs}"
    if c < 0.88:
        ps = ""
        if r.random() < 0.35:
            ps = "<" + ", ".join(name(r, True) for _ in range(r.randint(1, 2))) + ">"
            hit("struct:params")
        else:
            hit("struct:no_params")
        n = r.randint(0, 3)
        if n == 0:
            hit("struct:no_fields")
        fsep = ", "
        if n > 1 and r.random() < 0.25:
            fsep = "\n  , "
            hit("struct:newline_around_comma")
        fs = fsep.join(f"{name(r)}: {tsum(r)}" for _ in range(n))
        if n and r.random() < 0.2:
            fs += ","
            hit("struct:trailing_comma")
        nl = ""
        if r.random() < 0.3:
            nl = "\n  "
            hit("struct:multiline")
        hit("stmt:struct")
        return f"struct {name(r, True)}{ps} {{{nl}{fs}{nl}}}"
    ps = ""
    if r.random() < 0.4:
        ps = "<" + ", ".join(name(r, True) for _ in range(r.randint(1, 2))) + ">"
        hit("typedef:params")
    else:
        hit("typedef:no_params")
    hit("stmt:typedef")
    return f"type {name(r, True)}{ps} = {tsum(r)}"


def program(r):
    lines = []
    for _ in range(r.randint(1, 6)):
        if r.random() < 0.15:
            lines.append("")
            hit("trivia:blank_line")
        if r.random() < 0.12:
            lines.append("// a comment")
            hit("trivia:comment_line")
        s = stmt(r)
        if r.random() < 0.12 and "\n" not in s:
            s += "  // trailing"
            hit("trivia:comment_trailing")
        lines.append(s)
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    if sys.argv[1] == "--features":
        print("\n".join(ALL_FEATURES))
        raise SystemExit
    count = int(sys.argv[1])
    r = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 0)
    for i in range(count):
        if i:
            print("%%")
        sys.stdout.write(program(r))
