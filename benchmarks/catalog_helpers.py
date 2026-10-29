"""Helpers the benchmarks share: determining_equations and vanishes, formerly
in tests/test_symmetry_catalog.py (removed there in e477025, #4)."""

from sympy import Dummy, Pow, expand, numer, simplify, together

from delierium import (
    overdetermined_system_ode,
    overdetermined_system_odes,
    overdetermined_system_pde,
)


def determining_equations(entry, infinitesimals):
    """The determining equations of a catalogue entry."""
    indep, dep = entry.variables()
    eqs = entry.parsed_equations()
    if entry.kind == "ode":
        return overdetermined_system_ode(eqs[0], dep, indep, infinitesimals=infinitesimals)
    if entry.kind == "odes":
        return overdetermined_system_odes(eqs, dep, indep, infinitesimals=infinitesimals)
    return overdetermined_system_pde(eqs[0], dep, indep, infinitesimals=infinitesimals)


def vanishes(residue):
    """Whether residue is 0; powers with symbolic exponents as generators."""
    residue = simplify(residue)
    if residue == 0:
        return True
    generators, powers = {}, {}
    for p in residue.atoms(Pow):
        if not p.exp.is_number:
            n, s = p.exp.as_coeff_Add()
            powers[p] = generators.setdefault((p.base, s), Dummy()) * p.base**n
    return expand(numer(together(residue.xreplace(powers)))) == 0
