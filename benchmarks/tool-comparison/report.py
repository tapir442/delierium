"""BENCHMARK.md from the results in this directory (the runs of 2026-10-28 against
delierium 2.7.0): a summary per tool and one paragraph per catalogue entry where a tool
differs from delierium.

    uv run python benchmarks/tool-comparison/report.py > BENCHMARK.md
"""

import collections
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))

from sympy import Derivative, Function, Poly, Subs, Symbol, ode_order, sympify  # noqa: E402
from sympy.core.function import AppliedUndef  # noqa: E402

from tests.symmetry_catalog import CATALOG  # noqa: E402

CAT = {e.name: e for e in CATALOG}


def load(name):
    path = HERE / name
    return [json.loads(line) for line in open(path)] if path.exists() else []


def by_name(rows):
    return {r["name"]: r for r in rows if "name" in r}


def listed(value):
    """A list stored as a list or as its str()."""
    if value in (None, "", "None"):
        return []
    if isinstance(value, list):
        return value
    try:
        return eval(value, {}, {})  # noqa: S307  # our own str() of a list of str
    except Exception:  # noqa: BLE001
        return [value]


# ---------------------------------------------------------------- equation features


def compound_function(e):
    """An arbitrary function of an expression, f(y/x)."""
    indep, dep = e.variables()
    return any(
        isinstance(f, AppliedUndef) and f not in dep
        and not all(a.is_Symbol or a in dep for a in f.args)  # f(y) is no expression
        for q in e.parsed_equations()
        for f in q.atoms(AppliedUndef)
    )


def divergence_form(e):
    """A derivative of something else than an unknown, (u**s u_x)_x."""
    _, dep = e.variables()
    return any(
        not (isinstance(d.expr, AppliedUndef) and d.expr in dep)
        for q in e.parsed_equations()
        for d in q.atoms(Derivative)
    )


def nonlinear_first_order(e):
    if e.kind != "ode":
        return False
    (x,), (y,) = e.variables()
    q = e.parsed_equations()[0]
    if ode_order(q, y) != 1:
        return False
    p = Symbol("p")
    try:
        return Poly(q.subs(y.diff(x), p), p).degree() >= 2
    except Exception:  # noqa: BLE001
        return True


def polynomial_of_degree_2(generator, coordinates):
    try:
        return all(
            Poly(sympify(c), *coordinates).total_degree() <= 2 for c in generator
        )
    except Exception:  # noqa: BLE001
        return False


# ---------------------------------------------------------------- paragraphs


def readable(e, dep=()):
    """e (an expression or its string) in the notation of the text: y'' for a derivative of
    an unknown of one variable, u_xt for several, f'(x) for an arbitrary function, ^ for
    powers, spaces for products."""
    if isinstance(e, str):
        try:
            e = sympify(e)
        except Exception:  # noqa: BLE001
            return e.replace("**", "^").replace("*", " ")
    names = {f.func for f in dep}
    one_variable = all(len(f.args) == 1 for f in dep)
    replacements = {}
    for sub in e.atoms(Subs):  # f'(y/x) as Subs(Derivative(f(xi), xi), xi, y/x)
        if isinstance(sub.expr, Derivative) and isinstance(sub.expr.expr, AppliedUndef):
            n = sum(k for _, k in sub.expr.variable_count)
            point = ", ".join(readable(p, dep) for p in sub.point)
            replacements[sub] = Symbol(f"{sub.expr.expr.func.__name__}{chr(39) * n}({point})")
    e = e.xreplace(replacements)
    replacements = {}
    for d in sorted(e.atoms(Derivative), key=lambda d: -len(str(d))):
        f = d.expr
        if not isinstance(f, AppliedUndef):
            # divergence form: the derivative of an expression, (u^2 u_x)_x
            inner = f"({readable(f, dep)})"
            if one_variable:
                replacements[d] = Symbol(inner + "'" * sum(k for _, k in d.variable_count))
            else:
                replacements[d] = Symbol(inner + "_" + "".join(str(v) * k for v, k in d.variable_count))
            continue
        name = f.func.__name__
        if len(f.args) == 1:
            n = sum(k for _, k in d.variable_count)
            text = name + ("'" * n if n <= 4 else f"^({n})")
            if f.func not in names:
                text += f"({readable(f.args[0])})"
        else:
            text = name + "_" + "".join(str(v) * k for v, k in d.variable_count)
        replacements[d] = Symbol(text)
    e = e.xreplace(replacements)
    e = e.xreplace({f: Symbol(f.func.__name__) for f in e.atoms(AppliedUndef) if f.func in names})
    text = str(e).replace("**", "^").replace("*", " ")
    return text


def readable_equation(e):
    _, dep = e.variables()
    return "; ".join(f"{readable(q, dep)} = 0" for q in e.parsed_equations())



def fmt_gen(g):
    if isinstance(g, (list, tuple)):
        return "(" + ", ".join(readable(c) for c in g) + ")"
    if isinstance(g, str) and g.startswith("("):
        try:
            return "(" + ", ".join(readable(c) for c in sympify(g)) + ")"
        except Exception:  # noqa: BLE001
            return readable(g)
    return readable(str(g))


def heading(e):
    name = e.name.replace("**", "^")
    # the name often has the equation already (y'' = 0, CRC 1, 10.5: u_t = ...)
    eq = "" if "=" in name else f" {readable_equation(e)};"
    return f"**{name}**.{eq} dimension {e.dimension}."


def paragraph(e, facts, cause):
    """An entry: its heading and facts, under the cause (title, explanation, detail); the
    detail is what is particular to the entry."""
    if isinstance(cause, str):
        cause = (cause, "", "")
    title, explanation, detail = cause
    detail = detail.replace("**", "^")
    return {"title": title, "explanation": explanation.replace("**", "^"),
            "text": f"{heading(e)} {facts}{' ' + detail if detail else ''}\n",
            # the section names the tool: "LIEPDE: dimension 0." as "dimension 0"
            "generic": table_row(e, re.sub(r"^[\w -]+: ", "", facts).rstrip(".")
                                 .replace("|", "\\|") or "–",
                                 detail.replace("|", "\\|") or "–")}


def table_row(e, *cells):
    """The cells of an entry's table row: name, equation, dimension, then cells."""
    name = e.name.replace("**", "^")
    eq = readable_equation(e).replace("|", "\\|")
    return [name.split(":")[0] if "=" in name else name, eq, str(e.dimension), *cells]


GENERIC = ["entry", "equation", "dimension", "result", "note"]


def grouped(paras, level="####", header=None):
    """The entries under their causes, the most frequent cause first."""
    if not paras:
        return ["None.\n"]
    groups = collections.defaultdict(list)
    explanations = {}
    for p in paras:
        groups[p["title"]].append(p["text"])
        if p["explanation"] and not explanations.get(p["title"]):
            explanations[p["title"]] = p["explanation"]
    out = []
    rows = collections.defaultdict(list)
    for p in paras:
        if p.get("row"):
            rows[p["title"]].append(p["row"])
    for title, texts in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        out.append(f"{level} {title} ({len(texts)})\n")
        if explanations.get(title):
            out.append(explanations[title] + "\n")
        members = [p for p in paras if p["title"] == title]
        if header and len(rows[title]) == len(texts):
            cols, body = header, rows[title]
            if cols[-1] == "note" and all(r[-1] == "–" for r in body):
                cols, body = cols[:-1], [r[:-1] for r in body]
        elif all("generic" in p for p in members):
            cols, body = GENERIC, [p["generic"] for p in members]
            # drop the note column where no entry has a note
            if all(r[-1] == "–" for r in body):
                cols, body = cols[:-1], [r[:-1] for r in body]
        else:
            out += texts
            continue
        lines = ["| " + " | ".join(cols) + " |", "|" + "---|" * len(cols)]
        lines += ["| " + " | ".join(r) + " |" for r in body]
        out.append("\n".join(lines) + "\n")
    return out


RAW_ABS = set()


def raw_has_abs(tool):
    out = set()
    for r in load(f"{tool}-raw.jsonl"):
        m = re.search(r"under investigation is :\s*(.*?)\$", r.get("output", ""), re.S)
        if m and "abs(" in m.group(1):
            out.add(r["name"])
    return out


FRACTIONAL = {
    "Kamke 7.8": "y = v**(-2) gives v''' = 0; the generators with y**(3/2) are missing",
    "Kamke 7.9": "the generators with y**(5/3) are missing",
    "Kamke 6.157": "x y**(5/3) d/dy is missing",
    "Hydon Example 5.8: y'''' = y'''**(4/3)": "the scaling x d/dx is missing",
}
CRACK_RATIONAL = {
    "Kamke 6.186", "Kamke 6.195", "Bluman-Anco (3.413): y'' = 2 (x y' - y)(1 + y'**2)/(x**2 + y**2)",
}


LABEL = {"reduce": "LIEPDE", "relie": "ReLie", "dimsym": "DIMSYM", "spde": "SPDE"}


def reduce_cause(tool, e, row, has_abs):
    """(title, explanation, detail) of a difference between a REDUCE package and delierium."""
    label = LABEL[tool]
    name = e.name
    if tool == "spde":
        if row["status"] == "same dimension":
            return ("Wrong eta components",
                    "SPDE (version of November 1986) computes wrong eta components in today's "
                    "REDUCE, by its own result(): y'' = 0 gives x**2 d/dx - x y d/dy instead of "
                    "+ x y d/dy. The dimension is right, the generators are not.", "")
        d, x = row.get("dimension"), e.dimension
        if str(d) == "infinite" or (str(d).isdigit() and isinstance(x, int) and int(d) > x):
            return ("Remaining conditions incomplete",
                    "SPDE's remaining conditions are incomplete, so it reports more generators "
                    "than there are (its wrong eta components enter too).", "")
        if e.name.startswith(("CRC 1, 12.4: w_tt = F(w_xx)", "Gabel et al. 6")):
            return ("Non-polynomial function of a derivative",
                    "SPDE splits the determining equations only by polynomial dependence on the "
                    "derivatives; with F(w_xx) or exp(3 atan(u_x)) its conditions are wrong.", "")
        params = sorted({str(sym) for q in e.parsed_equations() for sym in q.free_symbols}
                        - set(e.independent))
        if params:
            return ("Generators that depend on the parameters lost",
                    "SPDE solves the determining equations for generic values of the parameters "
                    "and loses the generators that depend on them: scalings whose exponents "
                    "combine the parameters, factors like exp(-b m t).",
                    "Parameters: " + ", ".join(params) + ".")
        return ("Generators lost", "SPDE's solution of the determining equations loses "
                "generators; not traced further.", "")
    if name in has_abs:
        return ("abs() from REDUCE's simplification",
                f"REDUCE simplifies the power of a product with a fractional exponent in the input "
                f"to an expression with abs(u1); abs breaks the scalings, and {label} finds only "
                f"those that survive it.", "")
    if name in FRACTIONAL or name.startswith("CRC 1, 10.5: u_t = (u**(-4/3)"):
        detail = FRACTIONAL.get(name, "the generators with u**(-4/3) are missing")
        return ("Fractional powers missed by CRACK",
                f"CRACK (used by {label}) misses generators with fractional powers of the "
                f"dependent variable or of a derivative; DIMSYM finds them with the same input.",
                detail[0].upper() + detail[1:] + ".")
    if name in CRACK_RATIONAL:
        return ("Rational generators missed by CRACK",
                f"{label}'s solver CRACK does not find all rational generators; DIMSYM, with the "
                f"same input, finds them.", "")
    if name.startswith("Bluman-Anco Exercise 3.5-3"):
        return ("Trigonometric functions taken as independent",
                f"The equation has cot(y) and sin(y) cos(y) (REDUCE writes sin(2 u1)/2). "
                f"{label} splits the determining equations by them as independent functions "
                f"(DIMSYM's log: 'found special function: cot(u(1)) ... cos(2*u(1))'), without "
                f"cot = cos/sin and sin**2 + cos**2 = 1, so its conditions are too strong; the "
                f"equation is linearizable, dimension 8.", "")
    if name.startswith("PINNacle HeatND"):
        return ("Infinite part of a linear PDE lost",
                f"For a linear PDE the generators phi d/du, phi any solution of the equation, "
                f"make the algebra infinite; {label} returns the finite part only.", "")
    if name.startswith("Gabel et al. 7"):
        return ("Free functions with too many arguments",
                "ReLie takes the arguments of its free functions from REDUCE's global list after "
                "CRACK (fargs), which still has the variables CRACK started with: it returns "
                "f_1(x, t), i.e. infinitely many generators; with f_1 = f_1(x) its own condition "
                "gives the 5.", "")
    if compound_function(e):
        return ("Arbitrary function of an expression",
                f"An arbitrary function of an expression (f(y/x), f(x y' - y), ...): {label} takes "
                f"it as an opaque operator of the variables, without the chain rule, and its "
                f"splitting by the jet variables is too strong.", "")
    if name.startswith("EqWorld ODE 3.47"):
        return ("Linearizable ODE, no symmetry found",
                "Linearizable (u = int exp(-int f dy) dy gives u'' = g(x) u'); LIEPDE finds no "
                "symmetry, ReLie (also CRACK) the right dimension; not traced further.", "")
    return ("Not traced", "", "")


def reduce_paragraphs(tool):
    rows = load(f"{tool}.jsonl")
    has_abs = raw_has_abs(tool)
    out = []
    for row in rows:
        e = CAT.get(row["name"])
        if e is None:
            continue
        wrong = listed(row.get("wrong_generators"))
        missing = listed(row.get("catalogue_not_in_span"))
        different = row["status"] == "different dimension"
        if not (different or wrong or (row["status"] == "same dimension" and missing)):
            continue
        facts = []
        if different:
            facts.append(f"{LABEL[tool]}: dimension {row.get('dimension')}.")
        elif wrong:
            pass  # the right dimension: the rejected generators say what is wrong
        if wrong:
            facts.append("Rejected: "
                         + ", ".join(fmt_gen(g) for g in wrong[:6])
                         + (" ..." if len(wrong) > 6 else "") + ".")
        if missing:
            facts.append("Missing: "
                         + ", ".join(fmt_gen(g) for g in missing[:6])
                         + (" ..." if len(missing) > 6 else "") + ".")
        if row.get("closed") in (False, "False"):
            facts.append("Not closed.")
        cause = reduce_cause(tool, e, row, has_abs)
        para = paragraph(e, " ".join(facts), cause)
        if cause[0] == "Wrong eta components":
            para["row"] = table_row(
                e, ", ".join(fmt_gen(g) for g in wrong[:3]) + (" ..." if len(wrong) > 3 else ""),
                ", ".join(fmt_gen(g) for g in missing[:3]) + (" ..." if len(missing) > 3 else "")
                or "–",
                "no" if row.get("closed") in (False, "False") else "yes")
        out.append(para)
    return rows, out


def status_table(rows, extra=None):
    c = collections.Counter(r.get("status", "?") for r in rows)
    lines = ["| result | entries |", "|---|---|"]

    def short(status):
        m = re.match(r"(.*arbitrary function of )(.*)", status)
        if not m:
            return status
        y = Function("y")(Symbol("x"))
        return m.group(1) + readable(m.group(2), [y] if "y(x)" in m.group(2) else [])

    for k, v in c.most_common():
        lines.append(f"| {short(k)} | {v} |")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------- sections


def section_reduce(tool, title, intro):
    rows, paras = reduce_paragraphs(tool)
    text = [f"## {title}\n", intro + "\n", status_table(rows)]
    text.append(f"\n### Entries that differ ({len(paras)})\n")
    text += grouped(paras, header=["entry", "equation", "dimension", "rejected", "missing",
                                   "closed"])
    return "\n".join(text)


def mathlie_generator(g, e):
    """A MathLie generator (Mathematica InputForm) in the notation of the text."""
    sys.path.insert(0, str(HERE.parent))
    import mathlie_symmetries as ml  # noqa: PLC0415

    names = set(e.independent + e.dependent)
    names |= {str(sym) for q in e.parsed_equations() for sym in q.free_symbols}
    rename = {n: ml.safe(n) for n in names}
    try:
        return "(" + ", ".join(readable(ml.parse(c, rename)) for c in g) + ")"
    except Exception:  # noqa: BLE001
        return "(" + ", ".join(g) + ")"


def section_mathlie():
    rows = load("mathlie-compare.jsonl")
    raw = by_name(load("mathlie.jsonl"))
    out = []
    compared = 0
    status = collections.Counter()
    for row in rows:
        e = CAT.get(row["name"])
        if row.get("status") != "ok":
            status[row.get("status")] += 1
            continue
        if row.get("dimension") is None:
            status["remaining conditions not solvable for the comparison"] += 1
            continue
        compared += 1
        wrong = listed(row.get("wrong_generators"))
        missing = listed(row.get("catalogue_not_in_span"))
        same_dim = str(row.get("dimension")) == str(row.get("expected"))
        status["same dimension" if same_dim and not wrong else "different"] += 1
        if same_dim and not wrong and not missing:
            continue
        text = " ".join(" ".join(g) for g in listed(raw.get(e.name, {}).get("generators")))
        facts = [f"MathLie: dimension {row.get('dimension')}."]
        if wrong:
            gens = listed(raw.get(e.name, {}).get("generators"))
            facts.append("Rejected: " + ", ".join(
                mathlie_generator(gens[k], e) if k < len(gens) else str(k) for k in wrong) + ".")
        if missing:
            facts.append("Missing: "
                         + ", ".join(fmt_gen(g) for g in missing[:6]) + ".")
        params = sorted({str(sym) for q in e.parsed_equations() for sym in q.free_symbols}
                        - set(e.independent))
        if "Indeterminate" in text or "ComplexInfinity" in text:
            cause = ("Indeterminate in the generators",
                     "MathLie's generators contain Indeterminate or ComplexInfinity (from its "
                     "solution in hypergeometric functions), so they are no generators.", "")
        elif str(row.get("dimension")) == "infinite":
            cause = ("Too few conditions, infinite algebra",
                     "MathLie leaves too few conditions (xi, eta partly unresolved), so the "
                     "algebra comes out infinite.", "")
        elif params and e.kind == "pde" and missing:
            cause = ("Generators that depend on the parameters lost",
                     "MathLie solves the determining equations for generic values of the "
                     "parameters and misses the generators whose exponents or factors combine "
                     "them.", "Parameters: " + ", ".join(params) + ".")
        elif e.name.startswith("Bluman-Anco Exercise 3.5-3"):
            cause = ("Not traced",
                     "", "MathLie finds d/dx only; the equation is linearizable (dimension 8); "
                     "LIEPDE, ReLie and DIMSYM fail on it as well, through the trigonometric "
                     "functions.")
        else:
            cause = ("Determining equations not solved completely",
                     "MathLie does not solve the determining equations completely; the "
                     "generators it returns are correct.", "")
        out.append(paragraph(e, " ".join(facts), cause))
    text = ["## MathLie (Mathematica)\n",
            "Baumann's MathLie 3.0 under Mathematica 15.0, one kernel per entry, 120 s and "
            "8 GB (`benchmarks/mathlie_symmetries.py`; MathLie and its output are not "
            "redistributed). MathLie does not take first order ODEs. Where free functions or "
            "unsolved conditions remain, the dimension is the rank of the remaining conditions "
            "in an elimination Janet basis; where that is not possible (unsolved linear ODEs, "
            "special functions) the entry is not compared.\n",
            "| result | entries |", "|---|---|",
            *[f"| {k} | {v} |" for k, v in status.most_common()], "",
            f"### Entries that differ ({len(out)})\n"]
    return "\n".join(text + grouped(out))


def section_symmgrp():
    rows = load("symmgrp.jsonl")
    out = []
    for row in rows:
        if row["status"] != "different dimension":
            continue
        e = CAT[row["name"]]
        cause = (
            ("One branch of y'",
             "The equation is of degree >= 2 in y'; symmgrp needs it solved for y' and takes one "
             "root, a first order ODE in solved form, whose algebra is infinite. The whole "
             "equation has a finite algebra (delierium works with the equation as given).", "")
            if nonlinear_first_order(e)
            else ("Not traced", "", "")
        )
        para = paragraph(e, f"symmgrp: dimension {row.get('dimension')}.", cause)
        para["row"] = table_row(e, str(row.get("dimension")))
        out.append(para)
    text = ["## symmgrp2020 (Maxima)\n",
            "Hereman's symmgrp2020.max (Champagne, Hereman, Winternitz) computes the "
            "determining equations; delierium computes their Janet basis, so the comparison "
            "is by dimension (`benchmarks/symmgrp_symmetries.py`, 120 s). symmgrp splits only "
            "polynomial dependence on the derivatives, so equations with sqrt(u'), exp(u_x), "
            "F(u_x) keep derivatives in its determining equations; those are not compared.\n",
            status_table(rows), f"\n### Entries that differ ({len(out)})\n"]
    return "\n".join(text + grouped(out, header=["entry", "equation", "dimension", "symmgrp"]))


DIVERGENCE = ("Divergence form",
              "The equation is in divergence form, e.g. (u^s u_x)_x as an unevaluated Derivative "
              "of a product; sympy-extras does not evaluate it and returns transformations that "
              "are no symmetries (Upabjojr/sympy-extras#71).", "")
EXTRAS_BRANCH = ("One branch of y'",
                 "The equation is of degree >= 2 in y'; sympy-extras' generators and its check "
                 "are those of one branch only (Upabjojr/sympy-extras#72).", "")


def section_extras():
    rows = load("sympy-catalog.jsonl")
    tools = collections.defaultdict(dict)
    for r in rows:
        if r.get("tool"):
            tools[r["tool"]][r["name"]] = r
    detail = by_name(load("extras-detail.jsonl"))
    wrong_p, fewer_p, rejected_p = [], [], []
    for e in CATALOG:
        d = detail.get(e.name)
        g = tools["extras_gens"].get(e.name, {})
        flags = listed(g.get("ok")) if g.get("status") == "ok" else []
        rejected = [gen for gen, ok in zip(e.generators, flags) if ok in (False, "False")]
        if d and "error" not in d:
            if d["wrong"] or d["n"] > e.dimension:
                cause = (DIVERGENCE if divergence_form(e) else
                         EXTRAS_BRANCH if nonlinear_first_order(e) else ("Not traced", "", ""))
                k = len(d["wrong"])
                examples = ", ".join(fmt_gen(g) for g in d["wrong"][:2])
                facts = (f"sympy-extras: {d['n']} generator{'s' if d['n'] != 1 else ''}, {k} "
                         f"rejected" + (", e.g. " if k > 2 else ": ") + examples + ".")
                para = paragraph(e, facts, cause)
                para["row"] = table_row(e, str(d["n"]), str(k), examples + (" ..." if k > 2 else ""))
                wrong_p.append(para)
            elif d["n"] < e.dimension:
                indep, dep = e.variables()
                coords = [Symbol(v) for v in e.independent + e.dependent]
                outside = [g for g in e.generators if not polynomial_of_degree_2(g, coords)]
                facts = ("sympy-extras: no generators." if d["n"] == 0 else
                         f"sympy-extras: {d['n']} generator{'s' if d['n'] != 1 else ''}.")
                cause = ("Polynomial ansatz of degree <= 2",
                         "sympy-extras' ansatz has polynomials of degree <= 2 only, so it misses "
                         "the generators of higher degree or with other functions; the ones it "
                         "finds are correct. Where the published list has the missing generators, "
                         "they are named.",
                         ("Outside the ansatz: " + ", ".join(fmt_gen(g) for g in outside[:4])
                          + (" ..." if len(outside) > 4 else "") + "." if outside else ""))
                para = paragraph(e, facts, cause)
                para["row"] = table_row(
                    e, str(d["n"]),
                    ", ".join(fmt_gen(g) for g in outside[:3]) + (" ..." if len(outside) > 3 else "")
                    or "–")
                fewer_p.append(para)
        if rejected:
            cause = (("Divergence form",
                      "`check_symmetry` does not evaluate the outer derivative of an equation in "
                      "divergence form (Upabjojr/sympy-extras#71).", "") if divergence_form(e) else
                     EXTRAS_BRANCH if nonlinear_first_order(e) else
                     ("Not traced", "", "The residue has symbolic powers (((1 - x)/(1 + x))**A, "
                      "(1 + x)**A); delierium's check simplifies them, sympy-extras' does not.")
                     if e.name.startswith("Bluman-Anco (4.64)") else ("Not traced", "", ""))
            listed_gens = ", ".join(fmt_gen(g) for g in rejected)
            para = paragraph(e, "Rejected by `check_symmetry`: " + listed_gens + ".", cause)
            if not cause[2]:  # a detail of the entry needs the paragraph form
                para["row"] = table_row(e, str(len(e.generators)), str(len(rejected)), listed_gens)
            rejected_p.append(para)
    x = tools["extras"]
    finite = [e for e in CATALOG if isinstance(e.dimension, int)]
    ok = [e for e in finite if x.get(e.name, {}).get("status") == "ok"]
    same = sum(int(x[e.name]["n"]) == e.dimension for e in ok)
    text = ["## sympy-extras\n",
            "sympy-extras 0.0.2 (`symmetries`, `check_symmetry`): explicit generators by a "
            "polynomial ansatz of total degree <= 2, so a lower bound of the dimension "
            "(`benchmarks/sympy_symmetries.py`, 60 s per task).\n",
            "| | entries |", "|---|---|",
            f"| finite catalogue entries answered | {len(ok)} of {len(finite)} |",
            f"| as many generators as the dimension | {same} |",
            f"| fewer, all correct (degree <= 2) | {len(fewer_p)} |",
            f"| wrong generators | {len(wrong_p)} |",
            f"| published generators rejected by `check_symmetry` | {len(rejected_p)} entries |",
            "", f"### Wrong generators ({len(wrong_p)})\n",
            *grouped(wrong_p, header=["entry", "equation", "dimension", "generators", "rejected",
                                      "examples of rejected"]),
            f"### Published generators rejected ({len(rejected_p)})\n",
            "sympy-extras' `check_symmetry` rejects published generators that delierium "
            "confirms.\n",
            *grouped(rejected_p, header=["entry", "equation", "dimension", "published",
                                         "rejected", "rejected generators"]),
            f"### Fewer generators than the dimension ({len(fewer_p)})\n",
            *grouped(fewer_p, header=["entry", "equation", "dimension", "sympy-extras",
                                      "published generators outside the ansatz"])]
    tot, rej, kparas = extras_kamke()
    text += [f"### Kamke chapters 1 and 2\n",
             f"sympy-extras' generators of the first order ODEs, checked by delierium 2.7.0: "
             f"{tot} generators, {rej} rejected, all "
             f"in equations of degree >= 2 in y'.\n", *grouped(kparas, header=["entry", "equation", "generators", "rejected", "note"])]
    return "\n".join(text)


TEXTBOOK = {"1.38", "1.52", "1.81", "1.188", "1.189", "1.204", "1.206", "1.213", "1.237", "1.640"}
NAN = {"1.161", "1.193"}


def kamke():
    sys.path.insert(0, str(HERE.parent))
    import sympy_symmetries as ss  # noqa: PLC0415

    return ss.kamke_first_order(ss.DEFAULT_KAMKE)


def old_generators(path, tool):
    import sympy  # noqa: PLC0415
    from sympy.functions.elementary.piecewise import ExprCondPair  # noqa: PLC0415

    namespace = vars(sympy) | {"ExprCondPair": ExprCondPair}
    out = {}
    for r in load(path):
        if r.get("tool") == tool and r.get("suite") == "kamke" and r.get("generators"):
            try:
                out[r["name"]] = [tuple(eval(c, namespace) for c in g) for g in r["generators"]]  # noqa: S307
            except Exception:  # noqa: BLE001
                out[r["name"]] = [tuple(str(c) for c in g) for g in r["generators"]]
    return out


def kamke_paragraph(name, eq, label, gens, flags, cause):
    rejected = [g for g, ok in zip(gens, flags) if ok in (False, "False")]
    eq = f"{readable(eq, [Function('y')(Symbol('x'))])} = 0"
    title, explanation, detail = cause
    text = (f"**Kamke {name}**. {eq}. {label}: "
            f"{len(flags)} generator{'s' if len(flags) != 1 else ''}, rejected: "
            + ", ".join(fmt_gen(g) for g in rejected[:4])
            + (" ..." if len(rejected) > 4 else "") + "."
            + (f" {detail.replace('**', '^')}" if detail else "") + "\n")
    row = [f"Kamke {name}", eq.replace("|", "\\|"), str(len(flags)),
           ", ".join(fmt_gen(g) for g in rejected[:3]) + (" ..." if len(rejected) > 3 else ""),
           detail.replace("**", "^") or "–"]
    return {"title": title, "explanation": explanation.replace("**", "^"), "text": text,
            "row": row}


def branch(tool, issue):
    return ("One branch of y'",
            f"The ODE is of degree >= 2 in y'; {tool} solves it for y' and uses one root, so its "
            f"generators are symmetries of one branch only, not of the equation ({issue}). "
            f"delierium works with the equation as given.", "")


def section_sympy():
    rows = load("sympy-catalog.jsonl")
    a = [r for r in rows if r.get("tool") == "sympy_all"]
    c = collections.Counter(r["status"] for r in a)
    K = kamke()
    gens = old_generators(HERE.parent / "sympy_symmetries-2026-09-30.jsonl", "sympy_best")
    cross = [r for r in load("cross-kamke-deli.jsonl") if r.get("tool") == "cross_deli"]
    paras, tot, rej = [], 0, 0
    for r in sorted(cross, key=lambda r: [int(t) for t in r["name"].split(".")]):
        if r.get("status") != "ok":
            continue
        flags = listed(r.get("ok"))
        tot += len(flags)
        bad = sum(f in (False, "False") for f in flags)
        rej += bad
        if not bad:
            continue
        name = r["name"]
        if name in TEXTBOOK:
            cause = ("Generator fails the symmetry condition",
                     "SymPy's heuristic returns a generator that fails the textbook condition "
                     "eta_x + (eta_y - xi_x) F - xi_y F**2 - xi F_x - eta F_y = 0 for y' = F, "
                     "checked independently of delierium.", "")
        elif name in NAN:
            cause = ("nan as generator", "SymPy's heuristic returns (nan, nan).", "")
        elif name == "1.202":
            cause = ("Generator fails the symmetry condition", "",
                     "SymPy's generator has g(y), h(y) where the equation has g(x), h(x) (its "
                     "integral in y of an expression in x).")
        else:
            cause = branch("SymPy", "sympy/sympy#30643")
        paras.append(kamke_paragraph(name, K[name][0], "SymPy", gens.get(name, []), flags, cause))
    text = ["## SymPy\n",
            "SymPy 1.14.0 (`infinitesimals`, `checkinfsol`): some generators of first order "
            "ODEs by heuristics; everything else raises NotImplementedError "
            "(`benchmarks/sympy_symmetries.py`, 60 s per task).\n",
            "Catalogue (786 entries), `infinitesimals(hint=\"all\")`:\n",
            "| result | entries |", "|---|---|",
            *[f"| {k} | {v} |" for k, v in c.most_common()], "",
            f"Kamke chapters 1 and 2: SymPy's generators of the first order ODEs (every "
            f"heuristic separately), checked by "
            f"delierium 2.7.0: {tot} generators, {rej} rejected. Every rejection was checked "
            f"independently of delierium (the textbook condition for y' = F, or the branches); "
            f"delierium was right in all of them.\n",
            f"### Entries that differ ({len(paras)})\n", *grouped(paras, header=["entry", "equation", "generators", "rejected", "note"])]
    return "\n".join(text)


def extras_kamke():
    K = kamke()
    gens = old_generators(HERE.parent / "sympy_extras-2026-09-30.jsonl", "extras")
    cross = [r for r in load("cross-kamke.jsonl") if r.get("tool") == "cross_extras"]
    paras, tot, rej = [], 0, 0
    for r in sorted(cross, key=lambda r: [int(t) for t in r["name"].split(".")]):
        if r.get("status") != "ok":
            continue
        flags = listed(r.get("ok"))
        tot += len(flags)
        bad = sum(f in (False, "False") for f in flags)
        rej += bad
        if bad:
            paras.append(kamke_paragraph(
                r["name"], K[r["name"]][0], "sympy-extras", gens.get(r["name"], []), flags,
                branch("sympy-extras", "Upabjojr/sympy-extras#72")))
    return tot, rej, paras


def section_blad():
    rows = load("blad.jsonl")
    c = collections.Counter(
        "agree" if r.get("check") == "agree" else
        "differ" if r.get("status") == "ok" else
        "not supported (" + r["check"].split()[0] + ")" if r.get("status") == "unsupported" else
        r.get("status") for r in rows
    )
    differ = [r for r in rows if r.get("status") == "ok" and r.get("check") != "agree"]
    text = ["## BLAD (DifferentialAlgebra)\n",
            "Boulier's BLAD through DifferentialAlgebra: the Rosenfeld-Groebner decomposition of "
            "delierium's determining equations with an orderly ranking; the dimension is the "
            "number of parametric derivatives (`benchmarks/blad_crosscheck.py`, 300 s). BLAD "
            "takes rational coefficients only.\n",
            "| result | entries |", "|---|---|", *[f"| {k} | {v} |" for k, v in c.most_common()],
            "", f"### Entries that differ ({len(differ)})\n"]
    text += grouped([paragraph(CAT[r["name"]], str(r), ("Not traced", "", "")) for r in differ])
    return "\n".join(text)


def tool_counts():
    """(tool, what it computes, compared, same, differ) for the summary."""
    out = []
    cat = load("sympy-catalog.jsonl")
    x = {r["name"]: r for r in cat if r.get("tool") == "extras"}
    finite = [e for e in CATALOG if isinstance(e.dimension, int)]
    ok = [e for e in finite if x.get(e.name, {}).get("status") == "ok"]
    detail = by_name(load("extras-detail.jsonl"))
    wrong = sum(1 for d in detail.values() if "error" not in d and (d["wrong"] or d["n"] > CAT[d["name"]].dimension))
    out.append(("sympy-extras 0.0.2", "generators, polynomial ansatz of degree <= 2", len(ok),
                sum(int(x[e.name]["n"]) == e.dimension for e in ok), f"{wrong} wrong; fewer by design"))
    for tool, label, what in [
        ("reduce", "LIEPDE (REDUCE)", "generators (CRACK)"),
        ("relie", "ReLie 3.0 (REDUCE)", "generators (CRACK)"),
        ("dimsym", "DIMSYM 2.3 (REDUCE)", "generators"),
        ("spde", "SPDE 1986 (REDUCE)", "generators"),
    ]:
        rows = load(f"{tool}.jsonl")
        compared = [r for r in rows if r.get("status") in ("same dimension", "different dimension")]
        same = sum(r["status"] == "same dimension" and not listed(r.get("wrong_generators")) for r in compared)
        out.append((label, what, len(compared), same, len(compared) - same))
    rows = [r for r in load("mathlie-compare.jsonl")
            if r.get("status") == "ok" and r.get("dimension") is not None]
    same = sum(str(r["dimension"]) == str(r["expected"]) and not listed(r.get("wrong_generators"))
               for r in rows)
    out.append(("MathLie 3.0 (Mathematica 15.0)", "generators", len(rows), same, len(rows) - same))
    rows = load("symmgrp.jsonl")
    compared = [r for r in rows if r.get("status") in ("same dimension", "different dimension")]
    out.append(("symmgrp2020 (Maxima)", "determining equations", len(compared),
                sum(r["status"] == "same dimension" for r in compared),
                sum(r["status"] == "different dimension" for r in compared)))
    rows = load("blad.jsonl")
    compared = [r for r in rows if r.get("status") == "ok"]
    out.append(("BLAD (DifferentialAlgebra)", "Rosenfeld-Groebner, dimension", len(compared),
                sum(r.get("check") == "agree" for r in compared),
                sum(r.get("check") != "agree" for r in compared)))
    return out


HEADER = """# delierium compared with other tools

How delierium 2.7.0 compares with other programs for Lie point symmetries, Janet bases and
Lie algebras, on the 786 equations of its catalogue (`tests/symmetry_catalog.py`: 398 ODEs,
59 ODE systems, 329 PDEs from textbooks, handbooks, EqWorld and machine-learning
benchmarks, each with the dimension of its symmetry algebra and the published generators,
1790 in all; 611 entries have a finite algebra).

Every difference between a tool and delierium was checked against delierium's determining
equations: a generator is a symmetry if and only if it satisfies them, and the dimension is
that of the Janet basis. Where a tool and delierium disagreed, delierium was right. For
each catalogue entry where a tool differs there is a paragraph below: the
equation, the dimension, what the tool returned, the generators it got wrong or missed, and
the cause. The dimension given is the catalogue's, the same as delierium's; *rejected*
generators fail delierium's determining equations (no symmetries); *missing* are published
generators outside the span of the tool's generators; *not closed*: the tool's generators are
not closed under commutators. The sources of the equations are in `tests/symmetry_catalog.py`;
the Kamke equations of chapters 1 and 2 are those of SymPy's test suite.

**Setup.** 2026-10-28; AMD Ryzen 9 7900X (12 cores, 24 threads), 29 GB, Linux 7.0;
Python 3.14.4, SymPy 1.14.0, python-flint 0.9.0; delierium 2.7.0.
Every entry in its own process with a time limit (60 to 300 s, given per tool) and a memory
limit, at most 3 processes at a time, nice 19. The scripts are in `benchmarks/`, the raw
results in `benchmarks/tool-comparison/`; tools that may not be redistributed (MathLie,
ReLie, DIMSYM) are not included, nor their output.

"Not compared" covers what a tool cannot take (first order ODEs for MathLie, equations not
solved for a derivative, arbitrary functions of expressions for some), its timeouts, and
comparisons over the limits; such entries are counted in each tool's table but get no
paragraph.
"""


JANET = """## Janet bases, Groebner bases, Lie algebras

- **CoCoA 5.4 and Singular 4** (`benchmarks/cocoa_janet.py`): linear systems with constant
  coefficients are polynomial ideals, and the minimal reduced Janet basis of an ideal is
  unique for a term order. 207 systems (7 from the literature, 200 random): delierium's
  Janet basis, CoCoA's `JanetBasis` (JBMill) and Singular's `rJanet` are the same for all
  207.
- **Singular Plural** (`benchmarks/weyl_janet.py`): systems with polynomial coefficients as
  left ideals of the Weyl algebra (the Leibniz rule); each basis reduces the other to zero,
  and the leading derivatives agree. 205 systems: 199 agree, 0 differ, 6 Plural timeouts
  (60 s; delierium needs at most 0.9 s for them).
- **GAP 4** (`benchmarks/gap_lie_algebra.py`): for the 377 complete generator lists of finite
  algebras in the catalogue, delierium's structure constants as
  `LieAlgebraByStructureConstants`: derived and lower central series, solvability,
  nilpotency, center and Killing form agree for all 376 that GAP can take (1 skipped: the
  constants are not rational at the parameter values).
"""


TODAY = """## delierium alone

- Dimension: right for all 786 entries (`pytest -m slow`); all 1790 published generators
  confirmed by its determining equations.
- Generators by its solver (`lie_symmetries(...).generators()`): complete for 525 of the 611
  finite entries, all of them verified.
- `integrate_ode` with the catalogue's generators: 121 of the 176 ODEs solved.
- Not supported: systems of PDEs (#21); Painleve VI and EqWorld ODE 3.11 (the Janet basis
  exceeds 6 GB).
"""


REPRO = """## Reproduction

    benchmarks/tool-comparison/pipeline.sh     # all tools, about 4.5 hours at 3 processes
    benchmarks/tool-comparison/rerun.sh        # the stages repeated after the fix
    uv run python benchmarks/tool-comparison/report.py > BENCHMARK.md

The tools need local installations: REDUCE (with LIEPDE and SPDE; ReLie and DIMSYM from
their authors), Mathematica with MathLie, Maxima with symmgrp2020, CoCoA 5, Singular, GAP;
SymPy, sympy-extras and DifferentialAlgebra come from PyPI (`uv run --with ...`).
"""


def summary():
    lines = ["| tool | computes | entries compared | same as delierium | differ |",
             "|---|---|---|---|---|",
             "| SymPy 1.14 | some generators of first order ODEs | first order ODEs only | see below | see below |"]
    for label, what, n, same, differ in tool_counts():
        lines.append(f"| {label} | {what} | {n} | {same} | {differ} |")
    lines += ["| CoCoA 5.4, Singular 4 | Janet bases of polynomial ideals | 207 systems | 207 | 0 |",
              "| Singular Plural | Groebner bases in the Weyl algebra | 199 systems | 199 | 0 |",
              "| GAP 4 | Lie algebra invariants | 376 algebras | 376 | 0 |"]
    return "## Summary\n\n" + "\n".join(lines) + "\n"


def superscripts(text):
    """Every power x^e as x<sup>e</sup> (GitHub renders it as a real power): e is a
    parenthesized group (its parentheses dropped) or a number or name (1.5, n, sigma);
    powers in exponents too. Also <= and >= as signs."""
    out, i = [], 0
    while i < len(text):
        c = text[i]
        if c != "^":
            out.append(c)
            i += 1
            continue
        i += 1
        if i < len(text) and text[i] == "(":
            depth, j = 0, i
            while j < len(text):
                depth += {"(": 1, ")": -1}.get(text[j], 0)
                if depth == 0:
                    break
                j += 1
            exponent, i = text[i + 1 : j], j + 1
        else:
            m = re.match(r"-?[\w.]+", text[i:])
            exponent = m.group(0) if m else ""
            i += len(exponent)
        out.append(f"<sup>{superscripts(exponent)}</sup>")
    return "".join(out).replace(" <= ", " ≤ ").replace(" >= ", " ≥ ")


GREEK = {
    "alpha": "α", "beta": "β", "gamma": "γ", "delta": "δ", "epsilon": "ε", "zeta": "ζ",
    "eta": "η", "theta": "θ", "kappa": "κ", "lambda": "λ", "mu": "μ", "nu": "ν", "xi": "ξ",
    "pi": "π", "rho": "ρ", "sigma": "σ", "tau": "τ", "phi": "φ", "chi": "χ", "psi": "ψ",
    "omega": "ω", "Gamma": "Γ", "Delta": "Δ", "Lambda": "Λ", "Phi": "Φ", "Psi": "Ψ",
    "Omega": "Ω",
}


def markup(text):
    """Outside code spans: Greek names as letters (eta -> η), subscripts u_xx as
    u<sub>xx</sub>, powers as <sup>."""
    parts = text.split("`")
    for k in range(0, len(parts), 2):
        t = re.sub(r"(?<![A-Za-z])(" + "|".join(GREEK) + r")(?=\d|_|\b)",
                   lambda m: GREEK[m.group(1)], parts[k])
        t = re.sub(r"(?<![\w])([A-Za-zα-ωΑ-Ω]{1,6}\d*)_([A-Za-z0-9]{1,4})(?![\w])",
                   r"\1<sub>\2</sub>", t)
        # the outer derivative of divergence form, (u u_x)_x
        t = re.sub(r"([)\]])_([A-Za-z0-9]{1,4})(?![\w])", r"\1<sub>\2</sub>", t)
        t = re.sub(r"λ_(?![\w])", "λ", t)  # the parameter lambda_ (lambda is a keyword)
        parts[k] = superscripts(t)
    return "`".join(parts)


def main():
    parts = {}
    parts["sympy"] = section_sympy()
    parts["extras"] = section_extras()
    parts["reduce"] = section_reduce(
        "reduce", "LIEPDE (REDUCE)",
        "Thomas Wolf's LIEPDE, the determining equations solved by CRACK (REDUCE CSL rev. 7335, "
        "120 s; `benchmarks/reduce_symmetries.py`). The comparison checks the dimension, each "
        "generator against delierium's determining equations, the closure, and the published "
        "generators in the tool's span.")
    parts["relie"] = section_reduce(
        "relie", "ReLie (REDUCE)",
        "Francesco Oliveri's ReLie 3.0, also with CRACK (`benchmarks/relie_symmetries.py`; ReLie "
        "is not redistributed); compared as LIEPDE.")
    parts["dimsym"] = section_reduce(
        "dimsym", "DIMSYM (REDUCE)",
        "DIMSYM 2.3 (Sherring, Prince, Jerie), with its own solver (`benchmarks/dimsym_symmetries.py`; "
        "DIMSYM is not redistributed); compared as LIEPDE.")
    parts["spde"] = section_reduce(
        "spde", "SPDE (REDUCE)",
        "Fritz Schwarz's SPDE (1986), part of REDUCE (`benchmarks/spde_symmetries.py`); compared "
        "as LIEPDE.")
    parts["mathlie"] = section_mathlie()
    parts["symmgrp"] = section_symmgrp()
    parts["blad"] = section_blad()
    # a page break before each tool when printed (GitHub drops the style), a rule on screen
    page = '---\n\n<div style="page-break-before: always"></div>\n\n'
    tools = [page + part for part in parts.values()]
    print(markup("\n\n".join([HEADER, summary(), *tools, page + JANET, TODAY, REPRO])))


if __name__ == "__main__":
    main()
