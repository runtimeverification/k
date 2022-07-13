import logging
from collections import Counter
from typing import (
    Callable,
    Dict,
    Final,
    List,
    Mapping,
    Optional,
    Sequence,
    Tuple,
    Type,
    TypeVar,
)

from .cterm import CTerm, split_config_and_constraints
from .kast import (
    FALSE,
    TRUE,
    KApply,
    KAtt,
    KClaim,
    KDefinition,
    KFlatModule,
    KInner,
    KLabel,
    KRewrite,
    KRule,
    KRuleLike,
    KSequence,
    KToken,
    KVariable,
    Subst,
    WithKAtt,
    bottom_up,
    collect,
    flattenLabel,
    ktokenDots,
    top_down,
)
from .prelude import (
    Labels,
    Sorts,
    boolToken,
    build_assoc,
    mlAnd,
    mlBottom,
    mlEquals,
    mlEqualsTrue,
    mlImplies,
    mlOr,
    mlTop,
)
from .utils import find_common_items, hash_str, unique

_LOGGER: Final = logging.getLogger(__name__)

KI = TypeVar('KI', bound=KInner)
W = TypeVar('W', bound=WithKAtt)


def if_ktype(ktype: Type[KI], then: Callable[[KI], KInner]) -> Callable[[KInner], KInner]:
    def fun(term: KInner):
        if isinstance(term, ktype):
            return then(term)
        return term
    return fun


# TODO remove
def substitute(pattern: KInner, subst: Mapping[str, KInner]) -> KInner:
    if not isinstance(subst, Subst):
        subst = Subst(subst)
    return subst(pattern)


def bool_to_ml_pred(kast: KInner) -> KInner:
    return mlAnd([mlEqualsTrue(cond) for cond in flattenLabel('_andBool_', kast)])


def ml_pred_to_bool(kast: KInner, unsafe: bool = False) -> KInner:

    def _ml_constraint_to_bool(_kast: KInner) -> KInner:
        if type(_kast) is KApply:
            if _kast.label.name == '#Top':
                return TRUE
            if _kast.label.name == '#Bottom':
                return FALSE
            if _kast.label.name == '#Not':
                return KApply('notBool_', map(_ml_constraint_to_bool, _kast.args))
            if _kast.label.name == '#And':
                return KApply('_andBool_', map(_ml_constraint_to_bool, _kast.args))
            if _kast.label.name == '#Or':
                return KApply('_orBool_', map(_ml_constraint_to_bool, _kast.args))
            if _kast.label.name == '#Implies':
                return KApply('_impliesBool_', map(_ml_constraint_to_bool, _kast.args))
            if _kast.label.name == '#Equals':
                if _kast.args[0] == TRUE:
                    return _kast.args[1]
                if _kast.args[0] == FALSE:
                    return KApply(KLabel('notBool_'), [_kast.args[1]])
                if type(_kast.args[0]) in [KVariable, KToken]:
                    return KApply('_==K_', _kast.args)
            if unsafe:
                if _kast.label.name == '#Equals':
                    return KApply('_==K_', _kast.args)
                if _kast.label.name == '#Ceil':
                    ceil_var = abstract_term_safely(_kast, base_name='Ceil')
                    _LOGGER.warning(f'Converting #Ceil condition to variable {ceil_var.name}: {_kast}')
                    return ceil_var
                if _kast.label.name == '#Exists':
                    exists_var = abstract_term_safely(_kast, base_name='Exists')
                    _LOGGER.warning(f'Converting #Exists condition to variable {exists_var.name}: {_kast}')
                    return exists_var
        raise ValueError(f'Could not convert ML predicate to sort Bool: {_kast}')

    return _ml_constraint_to_bool(kast)


def simplifyBool(k):
    if k is None:
        return None
    simplifyRules = [ (KApply('_==K_', [KVariable('#LHS'), TRUE]), KVariable('#LHS'))                                                                               # noqa
                    , (KApply('_==K_', [TRUE, KVariable('#RHS')]), KVariable('#RHS'))                                                                               # noqa
                    , (KApply('_==K_', [KVariable('#LHS'), FALSE]), KApply('notBool_', [KVariable('#LHS')]))                                                        # noqa
                    , (KApply('_==K_', [FALSE, KVariable('#RHS')]), KApply('notBool_', [KVariable('#RHS')]))                                                        # noqa
                    , (KApply('notBool_', [FALSE]), TRUE)                                                                                                           # noqa
                    , (KApply('notBool_', [TRUE]), FALSE)                                                                                                           # noqa
                    , (KApply('notBool_', [KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')])]), KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('notBool_', [KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')])]), KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('notBool_', [KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')])]), KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('notBool_', [KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')])]), KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('_andBool_', [TRUE, KVariable('#REST')]), KVariable('#REST'))                                                                         # noqa
                    , (KApply('_andBool_', [KVariable('#REST'), TRUE]), KVariable('#REST'))                                                                         # noqa
                    , (KApply('_andBool_', [FALSE, KVariable('#REST')]), FALSE)                                                                                     # noqa
                    , (KApply('_andBool_', [KVariable('#REST'), FALSE]), FALSE)                                                                                     # noqa
                    , (KApply('_orBool_', [FALSE, KVariable('#REST')]), KVariable('#REST'))                                                                         # noqa
                    , (KApply('_orBool_', [KVariable('#REST'), FALSE]), KVariable('#REST'))                                                                         # noqa
                    , (KApply('_orBool_', [TRUE, KVariable('#REST')]), TRUE)                                                                                        # noqa
                    , (KApply('_orBool_', [KVariable('#REST'), TRUE]), TRUE)                                                                                        # noqa
                    ]                                                                                                                                               # noqa
    newK = k
    for rule in simplifyRules:
        rewrite = KRewrite(*rule)
        newK = rewrite(newK)
    return newK


def extract_lhs(term: KInner) -> KInner:
    return top_down(if_ktype(KRewrite, lambda rw: rw.lhs), term)


def extract_rhs(term: KInner) -> KInner:
    return top_down(if_ktype(KRewrite, lambda rw: rw.rhs), term)


def extract_subst(term: KInner) -> Tuple[Subst, KInner]:

    def _subst_for_terms(term1: KInner, term2: KInner) -> Optional[Subst]:
        if type(term1) is KVariable and type(term2) not in {KToken, KVariable}:
            return Subst({term1.name: term2})
        if type(term2) is KVariable and type(term1) not in {KToken, KVariable}:
            return Subst({term2.name: term1})
        return None

    def _extract_subst(conjunct: KInner) -> Optional[Subst]:
        if type(conjunct) is KApply:
            if conjunct.label.name == '#Equals':
                subst = _subst_for_terms(conjunct.args[0], conjunct.args[1])

                if subst is not None:
                    return subst

                if conjunct.args[0] == boolToken(True) and type(conjunct.args[1]) is KApply and conjunct.args[1].label.name in {'_==K_', '_==Int_'}:
                    subst = _subst_for_terms(conjunct.args[1].args[0], conjunct.args[1].args[1])

                    if subst is not None:
                        return subst

        return None

    conjuncts = flattenLabel('#And', term)
    subst = Subst()
    rem_conjuncts: List[KInner] = []

    for conjunct in conjuncts:
        new_subst = _extract_subst(conjunct)
        if new_subst is None:
            rem_conjuncts.append(conjunct)
        else:
            new_subst = subst.union(new_subst)
            if new_subst is None:
                raise ValueError('Conflicting substitutions')  # TODO handle this case
            subst = new_subst

    return subst, mlAnd(rem_conjuncts)


def count_vars(term: KInner) -> Counter:
    counter: Counter = Counter()

    def count(term: KInner) -> None:
        if type(term) is KVariable:
            counter[term.name] += 1

    collect(count, term)
    return counter


def collectFreeVars(kast):
    return list(count_vars(kast).keys())


def propagate_up_constraints(k):

    def _propagate_up_constraints(_k):
        if not (type(_k) is KApply and _k.label.name == '#Or'):
            return _k
        top_sort = _k.label.params[0]
        conjuncts1 = flattenLabel('#And', _k.args[0])
        conjuncts2 = flattenLabel('#And', _k.args[1])
        (common1, l1, r1) = find_common_items(conjuncts1, conjuncts2)
        (common2, r2, l2) = find_common_items(r1, l1)
        common = common1 + common2
        if len(common) == 0:
            return _k
        conjunct1 = mlAnd(l2, sort=top_sort)
        conjunct2 = mlAnd(r2, sort=top_sort)
        disjunct = mlOr([conjunct1, conjunct2], sort=top_sort)
        return mlAnd([disjunct] + common, sort=top_sort)

    return bottom_up(_propagate_up_constraints, k)


def splitConfigFrom(configuration):
    """Split the substitution from a given configuration.

    Given an input configuration `config`, will return a tuple `(symbolic_config, subst)`, where:

        1.  `config == substitute(symbolic_config, subst)`
        2.  `symbolic_config` is the same configuration structure, but where the contents of leaf cells is replaced with a fresh KVariable.
        3.  `subst` is the substitution for the generated KVariables back to the original configuration contents.
    """
    initial_substitution = {}

    def _mkCellVar(label):
        return label.replace('-', '_').replace('<', '').replace('>', '').upper() + '_CELL'

    def _replaceWithVar(k):
        if type(k) is KApply and k.is_cell:
            if k.arity == 1 and not (type(k.args[0]) is KApply and k.args[0].is_cell):
                config_var = _mkCellVar(k.label.name)
                initial_substitution[config_var] = k.args[0]
                return KApply(k.label, [KVariable(config_var)])
        return k

    symbolic_config = top_down(_replaceWithVar, configuration)
    return (symbolic_config, initial_substitution)


def collapseDots(kast):
    """Given a configuration with structural frames `...`, minimize the structural frames needed.

    -   Input: a configuration, potentially with structural frames.
    -   Output: the same configuration, with the amount of structural framing minimized.
    """
    def _collapseDots(_kast):
        if type(_kast) is KApply:
            if _kast.is_cell and _kast.arity == 1 and _kast.args[0] == ktokenDots:
                return ktokenDots
            newArgs = [arg for arg in _kast.args if arg != ktokenDots]
            if _kast.is_cell and len(newArgs) == 0:
                return ktokenDots
            if len(newArgs) < len(_kast.args):
                newArgs.append(ktokenDots)
            return _kast.let(args=newArgs)
        elif type(_kast) is KRewrite:
            if _kast.lhs == ktokenDots:
                return ktokenDots
        return _kast
    return bottom_up(_collapseDots, kast)


def push_down_rewrites(kast):

    def _flatten_ksequence(_kast):
        if type(_kast) is KSequence:
            new_items = []
            for item in _kast.items:
                if type(item) is KSequence:
                    new_items.extend(item.items)
                else:
                    new_items.append(item)
            return KSequence(new_items)
        return _kast

    def _push_down_rewrites(_kast):
        if type(_kast) is KRewrite:
            lhs = _kast.lhs
            rhs = _kast.rhs
            if lhs == rhs:
                return lhs
            if type(lhs) is KVariable and type(rhs) is KVariable and lhs.name == rhs.name:
                return lhs
            if type(lhs) is KApply and type(rhs) is KApply and lhs.label == rhs.label and lhs.arity == rhs.arity:
                newArgs = [KRewrite(lArg, rArg) for (lArg, rArg) in zip(lhs.args, rhs.args)]
                return lhs.let(args=newArgs)
            if type(lhs) is KSequence and type(rhs) is KSequence and lhs.arity > 0 and rhs.arity > 0:
                if lhs.arity == 1 and rhs.arity == 1:
                    return KRewrite(lhs.items[0], rhs.items[0])
                if lhs.items[0] == rhs.items[0]:
                    lowerRewrite = _push_down_rewrites(KRewrite(KSequence(lhs.items[1:]), KSequence(rhs.items[1:])))
                    return _flatten_ksequence(KSequence([lhs.items[0], lowerRewrite]))
                if lhs.items[-1] == rhs.items[-1]:
                    lowerRewrite = _push_down_rewrites(KRewrite(KSequence(lhs.items[0:-1]), KSequence(rhs.items[0:-1])))
                    return _flatten_ksequence(KSequence([lowerRewrite, lhs.items[-1]]))
            if type(lhs) is KSequence and lhs.arity > 0 and type(lhs.items[-1]) is KVariable and type(rhs) is KVariable and lhs.items[-1] == rhs:
                return KSequence([KRewrite(KSequence(lhs.items[0:-1]), KApply(Labels.EMPTY_K)), rhs])
        return _kast

    return top_down(_push_down_rewrites, kast)


def inlineCellMaps(kast):
    """Ensure that cell map collections are printed nicely, not as Maps."

    -   Input: kast term.
    -   Output: kast term with cell maps inlined.
    """
    def _inlineCellMaps(_kast):
        if type(_kast) is KApply and _kast.label.name.endswith('CellMapItem'):
            mapKey = _kast.args[0]
            if type(mapKey) is KApply and mapKey.is_cell:
                return _kast.args[1]
        return _kast
    return bottom_up(_inlineCellMaps, kast)


def removeSemanticCasts(kast):
    """Remove injected `#SemanticCast*` nodes in AST.

    -   Input: kast (possibly) containing automatically injected `#SemanticCast*` KApply nodes.
    -   Output: kast without the `#SemanticCast*` nodes.
    """
    def _removeSemanticCasts(_kast):
        if type(_kast) is KApply and _kast.arity == 1 and _kast.label.name.startswith('#SemanticCast'):
            return _kast.args[0]
        return _kast
    return bottom_up(_removeSemanticCasts, kast)


def markUselessVars(kast):
    """Given a kast term as input with variables, return one where the useless vars are appropriately marked.

    -   Input: A Kast term.
    -   Output: Kast term with variables appropriately named.
    """
    occurances = count_vars(kast)
    subst = {}
    for v in occurances:
        if v.startswith('_') and occurances[v] > 1:
            subst[v] = KVariable(v[1:])
        elif (not v.startswith('_')) and occurances[v] == 1:
            subst[v] = KVariable('_' + v)
    return substitute(kast, subst)


def uselessVarsToDots(kast, keepVars=None):
    """Structurally abstract away useless variables.

    -   Input: kast term, and a requires clause and ensures clause.
    -   Output: kast term with the useless vars structurally abstracted.
    """
    numOccurances = count_vars(kast) + Counter(keepVars)

    def _collapseUselessVars(_kast):
        if type(_kast) is KApply and _kast.is_cell:
            newArgs = []
            for arg in _kast.args:
                if type(arg) is KVariable and numOccurances[arg.name] == 1:
                    newArgs.append(ktokenDots)
                else:
                    newArgs.append(arg)
            return _kast.let(args=newArgs)
        return _kast

    return bottom_up(_collapseUselessVars, kast)


def labelsToDots(kast, labels):
    """Abstract specific labels for printing.

    -   Input: kast term, and list of labels to abstract.
    -   Output: kast term with those labels abstracted.
    """
    def _labelstoDots(k):
        if type(k) is KApply and k.is_cell and k.label.name in labels:
            return ktokenDots
        return k
    return bottom_up(_labelstoDots, kast)


def onAttributes(kast: W, f: Callable[[KAtt], KAtt]) -> W:
    kast = kast.map_att(f)

    # TODO mypy bug: https://github.com/python/mypy/issues/10817

    if type(kast) is KFlatModule:
        sentences = (sentence.map_att(f) for sentence in kast.sentences)
        return kast.let(sentences=sentences)  # type: ignore

    if type(kast) is KDefinition:
        modules = (module.map_att(f) for module in kast.modules)
        return kast.let(modules=modules)  # type: ignore

    return kast


def minimize_term(term, keep_vars=None, abstract_labels=[]):
    """Minimize a K term for pretty-printing.

    -   Input: kast term, and optionally requires and ensures clauses with constraints.
    -   Output: kast term minimized.
        -   Variables only used once will be removed.
        -   Unused cells will be abstracted.
        -   Attempt to remove useless conditions.
    """
    term = inlineCellMaps(term)
    term = removeSemanticCasts(term)
    term = uselessVarsToDots(term, keepVars=keep_vars)
    term = labelsToDots(term, abstract_labels)
    term = collapseDots(term)
    return term


def minimizeRule(rule, keepVars=[]):
    """Minimize a K rule or claim for pretty-printing.

    -   Input: kast representing a K rule or claim.
    -   Output: kast with the rule or claim minimized:
        -   Variables only used once will be removed.
        -   Unused cells will be abstracted.
        -   Attempt to remove useless side-conditions.
    """
    if not (type(rule) is KRule or type(rule) is KClaim):
        return rule

    ruleBody = rule.body
    ruleRequires = rule.requires
    ruleEnsures = rule.ensures

    ruleRequires = build_assoc(TRUE, '_andBool_', unique(flattenLabel('_andBool_', ruleRequires)))
    ruleRequires = simplifyBool(ruleRequires)

    ruleEnsures = build_assoc(TRUE, '_andBool_', unique(flattenLabel('_andBool_', ruleEnsures)))
    ruleEnsures = simplifyBool(ruleEnsures)

    constrainedVars = [] if keepVars is None else keepVars
    constrainedVars = constrainedVars + collectFreeVars(ruleRequires)
    constrainedVars = constrainedVars + collectFreeVars(ruleEnsures)
    ruleBody = minimize_term(ruleBody, keep_vars=constrainedVars)

    return rule.let(body=ruleBody, requires=ruleRequires, ensures=ruleEnsures)


def removeSourceMap(k):
    """Remove source map information from a given definition.

    Input: A JSON encoded K object.
    Output: The same JSON encoded object, with all source information stripped.
    """
    def _removeSourceMap(att):
        if type(att) is KAtt:
            atts = att.atts
            newAtts = {}
            for attKey in atts:
                if attKey != 'org.kframework.attributes.Source' and attKey != 'org.kframework.attributes.Location':
                    newAtts[attKey] = atts[attKey]
            return KAtt(atts=newAtts)
    return onAttributes(k, _removeSourceMap)


def remove_generated_cells(term: KInner) -> KInner:
    """Remove <generatedTop> and <generatedCounter> from a configuration.

    -   Input: Constrained term.
    -   Output: Constrained term with those cells removed.
    """
    rewrite = KRewrite(KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG'))
    return rewrite(term)


def isAnonVariable(kast):
    return type(kast) is KVariable and kast.name.startswith('_')


def omitLargeTokens(kast, maxLen=78):
    def _largeTokensToDots(_k):
        if type(_k) is KToken and len(_k.token) > maxLen:
            return KToken('...', _k.sort)
        return _k
    return bottom_up(_largeTokensToDots, kast)


def getCell(constrainedTerm, cellVariable):
    (state, _) = split_config_and_constraints(constrainedTerm)
    (_, subst) = splitConfigFrom(state)
    return subst[cellVariable]


def setCell(constrainedTerm, cellVariable, cellValue):
    (state, constraint) = split_config_and_constraints(constrainedTerm)
    (config, subst) = splitConfigFrom(state)
    subst[cellVariable] = cellValue
    return mlAnd([substitute(config, subst), constraint])


def removeUselessConstraints(constrainedTerm, keepVars=None):
    (state, constraint) = split_config_and_constraints(constrainedTerm)
    constraints = flattenLabel('#And', constraint)
    usedVars = collectFreeVars(state)
    usedVars = usedVars if keepVars is None else (usedVars + keepVars)
    prevLenUsedVars = 0
    newConstraints = []
    while len(usedVars) > prevLenUsedVars:
        prevLenUsedVars = len(usedVars)
        for c in constraints:
            if c not in newConstraints:
                newVars = collectFreeVars(c)
                if any([v in usedVars for v in newVars]):
                    newConstraints.append(c)
                    usedVars.extend(newVars)
        usedVars = list(set(usedVars))
    return mlAnd([state] + newConstraints)


def removeConstraintClausesFor(varNames, constraint):
    constraints = flattenLabel('#And', constraint)
    newConstraints = []
    for c in constraints:
        if not any([v in varNames for v in collectFreeVars(c)]):
            newConstraints.append(c)
    return mlAnd(newConstraints)


def removeConstraintsFor(varNames, constrainedTerm):
    (state, constraint) = split_config_and_constraints(constrainedTerm)
    constraint = removeConstraintClausesFor(varNames, constraint)
    return mlAnd([state, constraint])


def build_rule(
    rule_id: str,
    init_cterm: CTerm,
    final_cterm: CTerm,
    claim: bool = False,
    priority: Optional[int] = None,
    keep_vars: Optional[List[str]] = None
) -> Tuple[KRuleLike, Dict[str, KVariable]]:

    init_config, *init_constraints = init_cterm
    final_config, *final_constraints = final_cterm
    final_constraints = [c for c in final_constraints if c not in init_constraints]
    init_term = mlAnd([init_config] + init_constraints)
    final_term = mlAnd([final_config] + final_constraints)

    lhs_vars = collectFreeVars(init_term)
    rhs_vars = collectFreeVars(final_term)
    var_occurances = count_vars(mlAnd([push_down_rewrites(KRewrite(init_config, final_config))] + init_constraints + final_constraints, Sorts.GENERATED_TOP_CELL))
    v_subst: Dict[str, KVariable] = {}
    vremap_subst: Dict[str, KVariable] = {}
    for v in var_occurances:
        new_v = v
        if var_occurances[v] == 1:
            new_v = '_' + new_v
        if v in rhs_vars and v not in lhs_vars:
            new_v = '?' + new_v
        v_subst[v] = KVariable(new_v)
        vremap_subst[new_v] = KVariable(v)

    init_term = substitute(init_term, v_subst)
    final_term = applyExistentialSubstitutions(substitute(final_term, v_subst))
    (init_config, init_constraint) = split_config_and_constraints(init_term)
    (final_config, final_constraint) = split_config_and_constraints(final_term)

    rule_body = push_down_rewrites(KRewrite(init_config, final_config))
    rule_requires = simplifyBool(ml_pred_to_bool(init_constraint))
    rule_ensures = simplifyBool(ml_pred_to_bool(final_constraint))
    att_dict = {} if claim or priority is None else {'priority': str(priority)}
    rule_att = KAtt(atts=att_dict)

    rule: KRuleLike
    if not claim:
        rule = KRule(rule_body, requires=rule_requires, ensures=rule_ensures, att=rule_att)
    else:
        rule = KClaim(rule_body, requires=rule_requires, ensures=rule_ensures, att=rule_att)

    rule = rule.update_atts({'label': rule_id})
    new_keep_vars = None
    if keep_vars is not None:
        new_keep_vars = [v_subst[v].name for v in keep_vars]
    return (minimizeRule(rule, keepVars=new_keep_vars), vremap_subst)


def abstract_term_safely(kast: KInner, base_name: str = 'V') -> KVariable:
    vname = hash_str(kast)[0:8]
    return KVariable(base_name + '_' + vname)


def antiUnify(state1, state2):
    subst1 = {}
    subst2 = {}

    def _rewritesToAbstractions(_kast):
        if type(_kast) is KRewrite:
            return abstract_term_safely(_kast)
        return _kast

    minimizedRewrite = push_down_rewrites(KRewrite(state1, state2))
    abstractedState = bottom_up(_rewritesToAbstractions, minimizedRewrite)
    subst1 = abstractedState.match(state1)
    subst2 = abstractedState.match(state2)
    if subst1 is None or subst2 is None:
        raise ValueError('Anti-unification failed to produce a more general state!')
    return (abstractedState, subst1, subst2)


def antiUnifyWithConstraints(constrainedTerm1, constrainedTerm2, implications=False, disjunct=False):
    (state1, constraint1) = split_config_and_constraints(constrainedTerm1)
    (state2, constraint2) = split_config_and_constraints(constrainedTerm2)
    constraints1 = flattenLabel('#And', constraint1)
    constraints2 = flattenLabel('#And', constraint2)
    (state, subst1, subst2) = antiUnify(state1, state2)

    constraints = [c for c in constraints1 if c in constraints2]
    constraint1 = mlAnd([c for c in constraints1 if c not in constraints])
    constraint2 = mlAnd([c for c in constraints2 if c not in constraints])
    implication1 = mlImplies(constraint1, substToMlPred(subst1))
    implication2 = mlImplies(constraint2, substToMlPred(subst2))

    if implications:
        constraints.append(implication1)
        constraints.append(implication2)

    if disjunct:
        constraints.append(mlOr([constraint1, constraint2]))

    return mlAnd([state] + constraints)


def disjunct_constrained_terms(constrained_terms: Sequence[KInner], concave=False) -> KInner:
    if len(constrained_terms) == 0:
        return mlBottom()
    new_constrained_term = constrained_terms[0]
    for constrained_term in constrained_terms[1:]:
        new_constrained_term = antiUnifyWithConstraints(new_constrained_term, constrained_term, implications=concave, disjunct=concave)
    return new_constrained_term


def removeDisjuncts(constrainedTerm):
    clauses = flattenLabel('#And', constrainedTerm)
    clauses = [c for c in clauses if not (type(c) is KApply and c.label.name == '#Or')]
    constrainedTerm = mlAnd(clauses)
    return constrainedTerm


def applyExistentialSubstitutions(constrainedTerm):
    (state, constraint) = split_config_and_constraints(constrainedTerm)
    constraints = flattenLabel('#And', constraint)
    substPattern = mlEqualsTrue(KApply('_==K_', [KVariable('#VAR'), KVariable('#VAL')]))
    subst = {}
    newConstraints = []
    for c in constraints:
        substMatch = substPattern.match(c)
        if substMatch is not None and type(substMatch['#VAR']) is KVariable and substMatch['#VAR'].name.startswith('?'):
            subst[substMatch['#VAR'].name] = substMatch['#VAL']
        else:
            newConstraints.append(c)
    return substitute(mlAnd([state] + newConstraints), subst)


def constraintSubsume(constraint1, constraint2):
    if constraint1 == mlTop() or constraint1 == constraint2:
        return True
    elif type(constraint1) is KApply and constraint1.label.name == '#And':
        constraints1 = flattenLabel('#And', constraint1)
        if all([constraintSubsume(c, constraint2) for c in constraints1]):
            return True
    elif type(constraint1) is KApply and constraint1.label.name == '#Or':
        constraints1 = flattenLabel('#Or', constraint1)
        if any([constraintSubsume(c, constraint2) for c in constraints1]):
            return True
    elif type(constraint2) is KApply and constraint2.label.name == '#And':
        constraints2 = flattenLabel('#And', constraint2)
        if any([constraintSubsume(constraint1, c) for c in constraints2]):
            return True
    elif type(constraint2) is KApply and constraint2.label.name == '#Or':
        constraints2 = flattenLabel('#Or', constraint2)
        if all([constraintSubsume(constraint1, c) for c in constraints2]):
            return True
    else:
        return False


def matchWithConstraint(constrainedTerm1, constrainedTerm2):
    (state1, constraint1) = split_config_and_constraints(constrainedTerm1)
    (state2, constraint2) = split_config_and_constraints(constrainedTerm2)
    subst = state1.match(state2)
    if subst is not None and constraintSubsume(substitute(constraint1, subst), constraint2):
        return subst
    return None


def substToMlPred(subst):
    mlTerms = []
    for k in subst:
        if KVariable(k) != subst[k]:
            mlTerms.append(mlEquals(KVariable(k), subst[k]))
    return mlAnd(mlTerms)


def undoAliases(definition, kast):
    alias_undo_rewrites = [KRewrite(rule.body.rhs, rule.body.lhs) for module in definition for rule in module.rules if 'alias' in rule.att]
    newKast = kast
    for rewrite in alias_undo_rewrites:
        newKast = rewrite(newKast)
    return newKast
