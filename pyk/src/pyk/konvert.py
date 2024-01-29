from __future__ import annotations

import logging
from functools import reduce
from typing import TYPE_CHECKING

from .cterm import CTerm
from .kast import EMPTY_ATT, KAtt, KInner
from .kast.inner import KApply, KLabel, KSequence, KSort, KToken, KVariable
from .kast.manip import bool_to_ml_pred, extract_lhs, extract_rhs
from .kast.outer import KRule, KSyntaxSort
from .kore.prelude import BYTES as KORE_BYTES
from .kore.prelude import DOTK, SORT_K
from .kore.prelude import STRING as KORE_STRING
from .kore.syntax import (
    DV,
    And,
    App,
    Assoc,
    Axiom,
    Bottom,
    Ceil,
    Equals,
    EVar,
    Exists,
    Implies,
    Import,
    MLPattern,
    MLQuant,
    Module,
    Not,
    Rewrites,
    SortApp,
    SortDecl,
    String,
    Top,
)
from .prelude.bytes import BYTES, bytesToken_from_str, pretty_bytes_str
from .prelude.k import K_ITEM, K
from .prelude.ml import mlAnd, mlBottom, mlCeil, mlEquals, mlExists, mlImplies, mlNot, mlTop
from .prelude.string import STRING, pretty_string, stringToken
from .utils import FrozenDict

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator, Mapping
    from typing import Any, Final

    from .kast.outer import KDefinition, KFlatModule, KImport, KProduction, KSentence
    from .kore.kompiled import KompiledKore
    from .kore.syntax import Pattern, Sentence, Sort

_LOGGER: Final = logging.getLogger(__name__)


# --------------
# Module to KORE
# --------------


KORE_KEYWORDS: Final = {
    'alias',
    'axiom',
    'endmodule',
    'hooked-sort',
    'hooked-symbol',
    'module',
    'sort',
    'symbol',
}


def module_to_kore(definition: KDefinition) -> Module:
    """Convert the main module of a kompiled KAST definition to KORE format."""

    module = simplified_module(definition)

    name = name_to_kore(module.name)
    attrs = atts_to_kore({key: value for key, value in module.att.items() if key != 'digest'})  # filter digest

    imports = [Import('K')]
    sort_decls = [
        sort_decl_to_kore(syntax_sort)
        for syntax_sort in module.syntax_sorts
        if syntax_sort.sort.name not in [K.name, K_ITEM.name]
    ]

    sentences: list[Sentence] = []
    sentences += imports
    sentences += sort_decls

    return Module(name=name, sentences=sentences, attrs=attrs)


# TODO should this be used in _klabel_to_kore?
def name_to_kore(name: str) -> str:
    if name in KORE_KEYWORDS:
        return f"{name}'Kywd'"
    return munge(name)


def atts_to_kore(att: Mapping[str, Any]) -> list[App]:
    res = [att_to_kore(key, value) for key, value in att.items()]
    res.sort(key=lambda app: app.symbol)
    return res


def att_to_kore(key: str, value: Any) -> App:
    symbol = name_to_kore(key)

    if value == '':
        return App(symbol)

    parse_res = _parse_special_att_value(key, value)
    if parse_res is not None:
        sorts, args = parse_res
        return App(symbol, sorts, args)

    if isinstance(value, str):
        return App(symbol, (), (String(value),))

    if isinstance(value, FrozenDict) and 'node' in value:
        # TODO Should be kast_to_kore, but we do not have a KompiledKore.
        # TODO We should be able to add injections based on info in KDefinition.
        pattern = _kast_to_kore(KInner.from_dict(value))
        if not isinstance(pattern, App):
            raise ValueError('Expected application as attribure, got: {pattern.text}')
        return App(symbol, (), (pattern,))

    raise ValueError(f'Attribute conversion is not implemented for: {key}: {value}')


def _parse_special_att_value(key: str, value: Any) -> tuple[tuple[Sort, ...], tuple[Pattern, ...]] | None:
    if key == KAtt.LOCATION:
        assert isinstance(value, tuple)
        assert len(value) == 4
        loc_str = ','.join(str(loc) for loc in value)
        return (), (String(f'Location({loc_str})'),)
    if key == KAtt.SOURCE:
        assert isinstance(value, str)
        return (), (String(f'Source({value})'),)
    return None


def sort_decl_to_kore(syntax_sort: KSyntaxSort) -> SortDecl:
    name = 'Sort' + name_to_kore(syntax_sort.sort.name)
    attrs = atts_to_kore(syntax_sort.att)
    hooked = KAtt.HOOK in syntax_sort.att
    return SortDecl(name, (), attrs=attrs, hooked=hooked)


# ----------------------------------
# Module to KORE: KAST preprocessing
# ----------------------------------


COLLECTION_HOOKS: Final = {
    'SET.Set',
    'MAP.Map',
    'LIST.List',
    'ARRAY.Array',
    'RANGEMAP.RangeMap',
}


def simplified_module(definition: KDefinition, module_name: str | None = None) -> KFlatModule:
    """
    In ModuleToKORE.java, there are some implicit KAST-to-KAST kompilation
    steps hidden in the conversion. In particular, the kompiled KAST definition
    (compiled.json) is modular, whereas the kompiled definition
    (definition.kore) is flat.

    This function aims to factor out these hidden KAST-to-KAST kompilation
    steps so that our implementation of module_to_kore can be as simple as
    possible. Moreover, this has the potential to shed some light on how
    modules can be kompiled incrementally.

    This function is an approximation, i.e. there might be cases where it
    produces a different result to what would be expected based on kompile's
    output. These discrepancies should be analyzed and fixed.
    """
    module_name = module_name or definition.main_module_name
    module = _flatten_module(definition, module_name)  # TODO KORE supports imports, why is definition.kore flat?
    module = _add_syntax_sorts(module)
    module = _add_collection_atts(module)
    module = _add_domain_value_atts(module)
    return module


def _flatten_module(definition: KDefinition, module_name: str) -> KFlatModule:
    """Return a flat module with all sentences included and without imports"""
    module = definition.module(module_name)
    sentences = _imported_sentences(definition, module_name)
    return module.let(sentences=sentences, imports=())


def _imported_sentences(definition: KDefinition, module_name: str) -> list[KSentence]:
    """Return all sentences from imported modules, including the module itself."""

    pending: list[str] = [module_name]
    imported: set[str] = set()

    res: list[KSentence] = []
    while pending:
        module_name = pending.pop()
        if module_name in imported:
            continue
        module = definition.module(module_name)
        res += module.sentences
        pending += (importt.name for importt in module.imports)
        imported.add(module_name)

    return res


def _add_syntax_sorts(module: KFlatModule) -> KFlatModule:
    """Return a module with explicit syntax declarations: each sort is declared with the union of its attributes"""
    sentences = [sentence for sentence in module if not isinstance(sentence, KSyntaxSort)]
    sentences += _syntax_sorts(module)
    return module.let(sentences=sentences)


def _syntax_sorts(module: KFlatModule) -> list[KSyntaxSort]:
    """Return a declaration for each sort in the module"""
    declarations: dict[KSort, KAtt] = {}

    def is_higher_order(production: KProduction) -> bool:
        # Example: syntax {Sort} Sort ::= Sort "#as" Sort
        return production.sort in production.params

    # Merge attributes from KSyntaxSort instances
    for syntax_sort in module.syntax_sorts:
        sort = syntax_sort.sort
        if sort not in declarations:
            declarations[sort] = syntax_sort.att
        else:
            assert declarations[sort].keys().isdisjoint(syntax_sort.att)
            declarations[sort] = declarations[sort].update(syntax_sort.att)

    # Also consider production sorts
    for production in module.productions:
        if is_higher_order(production):
            continue

        sort = production.sort
        if sort not in declarations:
            declarations[sort] = EMPTY_ATT

    return [KSyntaxSort(sort, att=att) for sort, att in declarations.items()]


def _add_collection_atts(module: KFlatModule) -> KFlatModule:
    """Return a module where concat, element and unit attributes are added to collection sort declarations"""

    # Example: syntax Map ::= Map Map [..., klabel(_Map_), element(_|->_), unit(.Map), ...]
    concat_prods = {prod.sort: prod for prod in module.productions if KAtt.ELEMENT in prod.att}

    assert all(
        KAtt.UNIT in prod.att for _, prod in concat_prods.items()
    )  # TODO Could be saved with a different attribute structure: concat(Element, Unit)

    def update_att(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KSyntaxSort):
            return sentence

        syntax_sort: KSyntaxSort = sentence

        if syntax_sort.att.get(KAtt.HOOK) not in COLLECTION_HOOKS:
            return syntax_sort

        prod_att = concat_prods[syntax_sort.sort].att

        # TODO Here, attriubtes are stored as dict, but ultimately we should parse known attributes in KAtt.from_dict
        return syntax_sort.let(
            att=syntax_sort.att.update(
                {
                    KAtt.CONCAT: KApply(prod_att[KAtt.KLABEL]).to_dict(),
                    KAtt.ELEMENT: KApply(prod_att[KAtt.ELEMENT]).to_dict(),
                    KAtt.UNIT: KApply(prod_att[KAtt.UNIT]).to_dict(),
                }
            )
        )

    sentences = tuple(update_att(sent) for sent in module)
    return module.let(sentences=sentences)


def _add_domain_value_atts(module: KFlatModule) -> KFlatModule:
    """
    Return a module where attribute "hasDomainValues" is added to all
    sort declarations that either have the "token" attribute directly,
    or on a corresponding production.
    """

    token_sorts = _token_sorts(module)

    def update_att(sentence: KSentence) -> KSentence:
        if not isinstance(sentence, KSyntaxSort):
            return sentence

        syntax_sort: KSyntaxSort = sentence

        if syntax_sort.sort not in token_sorts:
            return syntax_sort

        return syntax_sort.let(att=syntax_sort.att.update({KAtt.HAS_DOMAIN_VALUES: ''}))

    sentences = tuple(update_att(sent) for sent in module)
    return module.let(sentences=sentences)


def _token_sorts(module: KFlatModule) -> set[KSort]:
    res: set[KSort] = set()

    # TODO "token" should be an attribute of only productions
    for syntax_sort in module.syntax_sorts:
        if KAtt.TOKEN in syntax_sort.att:
            res.add(syntax_sort.sort)

    for production in module.productions:
        if KAtt.TOKEN in production.att:
            res.add(production.sort)

    return res


# ------------
# KAST-to-KORE
# ------------

ML_CONN_LABELS: Final = {
    '#Top': r'\top',
    '#Bottom': r'\bottom',
    '#Not': r'\not',
    '#And': r'\and',
    '#Or': r'\or',
    '#Implies': r'\implies',
    '#Iff': r'\iff',
}

ML_QUANT_LABELS: Final = {
    '#Exists': r'\exists',
    '#Forall': r'\forall',
}

ML_PRED_LABELS: Final = {
    '#Ceil': r'\ceil',
    '#Floor': r'\floor',
    '#Equals': r'\equals',
    '#In': r'\in',
}

ML_PATTERN_LABELS: Final = dict(
    **ML_CONN_LABELS,
    **ML_QUANT_LABELS,
    **ML_PRED_LABELS,
)


def kast_to_kore(
    kast_defn: KDefinition,
    kompiled_kore: KompiledKore,
    kast: KInner,
    sort: KSort | None = None,
) -> Pattern:
    if sort is None:
        sort = K
    kast = kast_defn.add_ksequence_under_k_productions(kast)
    kast = kast_defn.sort_vars(kast, sort)
    kast = kast_defn.add_cell_map_items(kast)
    kast = kast_defn.add_sort_params(kast)
    kore = _kast_to_kore(kast)
    kore = kompiled_kore.add_injections(kore, _ksort_to_kore(sort))
    return kore


# 'krule' should have sorts on variables
def krule_to_kore(kast_defn: KDefinition, kompiled_kore: KompiledKore, krule: KRule) -> Axiom:
    krule_body = krule.body
    krule_lhs = CTerm(extract_lhs(krule_body), [bool_to_ml_pred(krule.requires)])
    krule_rhs = CTerm(extract_rhs(krule_body), [bool_to_ml_pred(krule.ensures)])

    top_level_kore_sort = SortApp('SortGeneratedTopCell')
    top_level_k_sort = KSort('GeneratedTopCell')
    # The backend does not like rewrite rules without a precondition
    if len(krule_lhs.constraints) > 0:
        kore_lhs0: Pattern = kast_to_kore(kast_defn, kompiled_kore, krule_lhs.kast, sort=top_level_k_sort)
    else:
        kore_lhs0 = And(
            top_level_kore_sort,
            (
                kast_to_kore(kast_defn, kompiled_kore, krule_lhs.kast, sort=top_level_k_sort),
                Top(top_level_kore_sort),
            ),
        )

    kore_rhs0: Pattern = kast_to_kore(kast_defn, kompiled_kore, krule_rhs.kast, sort=top_level_k_sort)

    kore_lhs = kompiled_kore.add_injections(kore_lhs0, sort=top_level_kore_sort)
    kore_rhs = kompiled_kore.add_injections(kore_rhs0, sort=top_level_kore_sort)
    prio = krule.priority
    attrs = [App(symbol='priority', sorts=(), args=(String(str(prio)),))]
    if 'label' in krule.att:
        label = krule.att['label']
        attrs.append(App(symbol='label', sorts=(), args=(String(label),)))
    axiom = Axiom(
        vars=(),
        pattern=Rewrites(
            sort=top_level_kore_sort,
            left=kore_lhs,
            right=kore_rhs,
        ),
        attrs=attrs,
    )
    return axiom


def kflatmodule_to_kore(kast_defn: KDefinition, kompiled_kore: KompiledKore, kflatmodule: KFlatModule) -> Module:
    kore_axioms: list[Sentence] = []
    for sent in kflatmodule.sentences:
        if type(sent) is not KRule:
            raise ValueError(f'Cannot convert sentence to Kore: {sent}')
        kore_axioms.append(krule_to_kore(kast_defn, kompiled_kore, sent))
    imports: list[Sentence] = [_kimport_to_kore(kimport) for kimport in kflatmodule.imports]
    return Module(name=kflatmodule.name, sentences=(imports + kore_axioms))


def _kimport_to_kore(kimport: KImport) -> Import:
    return Import(module_name=kimport.name, attrs=())


def _ksort_to_kore(ksort: KSort) -> SortApp:
    return SortApp('Sort' + ksort.name)


def _kast_to_kore(term: KInner) -> Pattern:
    stack: list = [term, []]
    while True:
        patterns = stack[-1]
        term = stack[-2]
        idx = len(patterns) - len(term.terms)
        if not idx:
            stack.pop()
            stack.pop()
            pattern = _kinner_to_kore(term, patterns)
            if not stack:
                return pattern
            stack[-1].append(pattern)
        else:
            stack.append(term.terms[idx])
            stack.append([])


def _kinner_to_kore(kinner: KInner, patterns: list[Pattern]) -> Pattern:
    match kinner:
        case KToken():
            assert not patterns
            return _ktoken_to_kore(kinner)
        case KVariable():
            assert not patterns
            return _kvariable_to_kore(kinner)
        case KSequence():
            return _ksequence_to_kore(kinner, patterns)
        case KApply():
            return _kapply_to_kore(kinner, patterns)
        case _:
            raise ValueError(f'Unsupported KInner: {kinner}')


def _ktoken_to_kore(ktoken: KToken) -> DV:
    value: String
    if ktoken.sort == STRING:
        value = String(pretty_string(ktoken))
    elif ktoken.sort == BYTES:
        value = String(pretty_bytes_str(ktoken))
    else:
        value = String(ktoken.token)

    sort = _ksort_to_kore(ktoken.sort)

    return DV(sort, value)


def _kvariable_to_kore(kvar: KVariable) -> EVar:
    sort: Sort
    if kvar.sort:
        sort = _ksort_to_kore(kvar.sort)
    else:
        sort = SORT_K
    return EVar('Var' + munge(kvar.name), sort)


def _ksequence_to_kore(kseq: KSequence, patterns: list[Pattern]) -> Pattern:
    if not patterns:
        return DOTK

    unit: Pattern
    args: list[Pattern]

    last = patterns[-1]
    if type(last) is EVar and last.sort == SORT_K:
        unit = last
        args = patterns[:-1]
    else:
        unit = DOTK
        args = patterns

    args.reverse()
    return reduce(lambda x, y: App('kseq', (), (y, x)), args, unit)


def _kapply_to_kore(kapply: KApply, patterns: list[Pattern]) -> Pattern:
    if kapply.label.name in ML_QUANT_LABELS:
        return _kapply_to_ml_quant(kapply, patterns)

    return _kapply_to_pattern(kapply, patterns)


def _kapply_to_ml_quant(kapply: KApply, patterns: list[Pattern]) -> MLQuant:
    label = kapply.label
    symbol = ML_QUANT_LABELS[label.name]
    sorts = tuple(_ksort_to_kore(ksort) for ksort in label.params)
    return MLQuant.of(symbol, sorts, patterns)


def _kapply_to_pattern(kapply: KApply, patterns: list[Pattern]) -> Pattern:
    label = kapply.label
    symbol = _label_to_kore(label.name)
    sorts = tuple(_ksort_to_kore(ksort) for ksort in label.params)

    if label.name in ML_PATTERN_LABELS:
        return MLPattern.of(symbol, sorts, patterns)

    return App(symbol, sorts, patterns)


def _label_to_kore(label: str) -> str:
    if label in ML_PATTERN_LABELS:
        return ML_PATTERN_LABELS[label]

    return 'Lbl' + munge(label)


# ------------
# KORE-to-KAST
# ------------


def kore_to_kast(kast_defn: KDefinition, kore: Pattern) -> KInner:
    kast = _kore_to_kast(kore)
    return kast_defn.remove_cell_map_items(kast)


def _kore_to_kast(pattern: Pattern) -> KInner:
    stack: list = [pattern.pattern if isinstance(pattern, Assoc) else pattern, []]
    while True:
        terms = stack[-1]
        pattern = stack[-2]
        patterns = pattern.patterns
        idx = len(terms) - len(patterns)
        if not idx:
            stack.pop()
            stack.pop()
            term = _pattern_to_kast(pattern, terms)
            if not stack:
                return term
            stack[-1].append(term)
        else:
            pattern = patterns[idx]
            stack.append(pattern.pattern if isinstance(pattern, Assoc) else pattern)
            stack.append([])


def _pattern_to_kast(pattern: Pattern, terms: list[KInner]) -> KInner:
    match pattern:
        case DV(sort, String(value)):
            assert not terms
            if sort == KORE_STRING:
                return stringToken(value)
            if sort == KORE_BYTES:
                return bytesToken_from_str(value)
            return KToken(value, _sort_to_kast(sort))

        case EVar(name, sort):
            assert not terms
            return KVariable(name=unmunge(name[3:]), sort=_sort_to_kast(sort))

        case App(symbol, sorts, _):
            if symbol == 'inj':
                _, _ = sorts
                (term,) = terms
                return term

            elif not sorts:
                if symbol == 'dotk':
                    () = terms
                    return KSequence(())

                elif symbol == 'kseq':
                    _, _ = terms
                    return KSequence(terms)

                else:
                    klabel = KLabel(unmunge(symbol[3:]))
                    return KApply(klabel, terms)

            # hardcoded polymorphic operators
            elif (
                symbol
                == "Lbl'Hash'if'UndsHash'then'UndsHash'else'UndsHash'fi'Unds'K-EQUAL-SYNTAX'Unds'Sort'Unds'Bool'Unds'Sort'Unds'Sort"
            ):
                (sort,) = sorts
                klabel = KLabel(unmunge(symbol[3:]), (_sort_to_kast(sort),))
                return KApply(klabel, terms)

            else:
                raise ValueError(f'Unsupported polymorphic operator: {symbol}')

        case Top(sort):
            assert not terms
            return mlTop(sort=_sort_to_kast(sort))

        case Bottom(sort):
            assert not terms
            return mlBottom(sort=_sort_to_kast(sort))

        case And(sort, _):
            return mlAnd(terms, sort=_sort_to_kast(sort))

        case Implies(sort, _, _):
            larg, rarg = terms
            return mlImplies(larg, rarg, sort=_sort_to_kast(sort))

        case Not(sort, _):
            (karg,) = terms
            return mlNot(karg, sort=_sort_to_kast(sort))

        case Exists(sort, EVar(vname, vsort), _):
            kvar = KVariable(name=unmunge(vname[3:]), sort=_sort_to_kast(vsort))
            (body,) = terms
            return mlExists(kvar, body, sort=_sort_to_kast(sort))

        case Equals(op_sort, sort, _, _):
            larg, rarg = terms
            return mlEquals(
                larg,
                rarg,
                arg_sort=_sort_to_kast(op_sort),
                sort=_sort_to_kast(sort),
            )

        case Ceil(op_sort, sort, _):
            (karg,) = terms
            return mlCeil(
                karg,
                arg_sort=_sort_to_kast(op_sort),
                sort=_sort_to_kast(sort),
            )

        case _:
            raise ValueError(f'Unsupported Pattern: {pattern}')


def _sort_to_kast(sort: Sort) -> KSort:
    if not isinstance(sort, SortApp) or not sort.name.startswith('Sort'):
        raise ValueError(f'Unsupported Sort: {sort}')
    return KSort(sort.name[4:])


# --------------
# Symbol munging
# --------------

UNMUNGE_TABLE: Final[FrozenDict[str, str]] = FrozenDict(
    {
        'Spce': ' ',
        'Bang': '!',
        'Quot': '"',
        'Hash': '#',
        'Dolr': '$',
        'Perc': '%',
        'And-': '&',
        'Apos': "'",
        'LPar': '(',
        'RPar': ')',
        'Star': '*',
        'Plus': '+',
        'Comm': ',',
        'Stop': '.',
        'Slsh': '/',
        'Coln': ':',
        'SCln': ';',
        '-LT-': '<',
        'Eqls': '=',
        '-GT-': '>',
        'Ques': '?',
        '-AT-': '@',
        'LSqB': '[',
        'RSqB': ']',
        'Bash': '\\',
        'Xor-': '^',
        'Unds': '_',
        'BQuo': '`',
        'LBra': '{',
        'Pipe': '|',
        'RBra': '}',
        'Tild': '~',
    }
)


MUNGE_TABLE: Final[FrozenDict[str, str]] = FrozenDict({v: k for k, v in UNMUNGE_TABLE.items()})


def munge(label: str) -> str:
    symbol = ''
    quot = False
    for c in label:
        if c in MUNGE_TABLE:
            symbol += "'" if not quot else ''
            symbol += MUNGE_TABLE[c]
            quot = True
        else:
            symbol += "'" if quot else ''
            symbol += c
            quot = False
    symbol += "'" if quot else ''
    return symbol


def unmunge(symbol: str) -> str:
    return ''.join(unmunged(symbol))


def unmunged(it: Iterable[str]) -> Iterator[str]:
    it = iter(it)

    startquote = False
    quote = False
    endquote = False
    buff: list[str] = []
    cnt = 0  # len(buff)

    for c in it:
        if c == "'":
            if startquote:
                raise ValueError('Empty quoted section')
            elif quote:
                if cnt == 0:
                    quote = False
                    endquote = True
                else:
                    fragment = ''.join(buff)
                    raise ValueError(f'Unexpected end of symbol: {fragment}')
            elif endquote:
                raise ValueError('Quoted sections next to each other')
            else:
                quote = True
                startquote = True

        else:
            startquote = False
            endquote = False
            if quote:
                if cnt == 3:
                    buff.append(c)
                    munged = ''.join(buff)
                    buff = []
                    cnt = 0
                    if not munged in UNMUNGE_TABLE:
                        raise ValueError(f'Unknown encoding "{munged}"')
                    yield UNMUNGE_TABLE[munged]
                else:
                    buff += [c]
                    cnt += 1
            else:
                yield c

    if quote:
        raise ValueError('Unterminated quoted section')
