from collections import Counter

from pyk.kast import KApply, KInner, KRewrite, KSequence, KVariable, top_down
from pyk.kastManip import if_ktype


def count_rhs_vars(term: KInner) -> Counter:
    def recur(term: KInner, *, rhs=False) -> Counter:
        if type(term) is KVariable:
            return Counter(term.name) if rhs else Counter()
        if type(term) is KRewrite:
            return recur(term.rhs, rhs=True)
        if type(term) is KApply:
            return sum((recur(t, rhs=rhs) for t in term.args), Counter())
        if type(term) is KSequence:
            return sum((recur(t, rhs=rhs) for t in term.items), Counter())
        return Counter()
    return recur(term)


def drop_var_prefixes(term: KInner) -> KInner:
    term = top_down(if_ktype(KVariable, drop_ques), term)
    term = top_down(if_ktype(KVariable, drop_unds), term)
    return term


def drop_ques(variable: KVariable) -> KVariable:
    if variable.name.startswith('?'):
        return variable.let(name=variable.name[1:])
    return variable


def drop_unds(variable: KVariable) -> KVariable:
    if variable.name.startswith('_'):
        return variable.let(name=variable.name[1:])
    return variable
