from collections import Counter
from typing import Callable, Dict, Mapping, Sequence, Tuple, Type, TypeVar

from .cli_utils import fatal
from .kast import (
    KApply,
    KAtt,
    KClaim,
    KDefinition,
    KFlatModule,
    KInner,
    KRewrite,
    KRule,
    KRuleLike,
    KSequence,
    KToken,
    KVariable,
    WithKAtt,
    bottom_up,
    collect,
    flattenLabel,
    klabelEmptyK,
    ktokenDots,
    top_down,
)
from .prelude import (
    buildAssoc,
    mlAnd,
    mlBottom,
    mlEquals,
    mlEqualsTrue,
    mlImplies,
    mlOr,
    mlTop,
)
from .subst import Subst, match
from .utils import dedupe, find_common_items, hash_str

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


def whereMatchingBottomUp(effect, matchPattern, pattern):
    def _effect(k):
        matchingSubst = match(matchPattern, k)
        newK = k
        if matchingSubst is not None:
            newK = effect(matchingSubst)
        return newK
    return bottom_up(_effect, pattern)


def replaceKLabels(pattern, klabelMap):
    def replace(k):
        if type(k) is KApply and k.label in klabelMap:
            return k.let(label=klabelMap[k.label])
        return k
    return bottom_up(replace, pattern)


def rewriteWith(rule, pattern):
    """Rewrite a given pattern at the top with the supplied rule.

    -   Input: A rule to rewrite with and a pattern to rewrite.
    -   Output: The pattern with the rewrite applied once at the top.
    """
    (ruleLHS, ruleRHS) = rule
    matchingSubst = match(ruleLHS, pattern)
    if matchingSubst is not None:
        return substitute(ruleRHS, matchingSubst)
    return pattern


def rewriteAnywhereWith(rule, pattern):
    """Attempt rewriting once at every position in an AST bottom-up.

    -   Input: A rule to rewrite with, and a pattern to rewrite.
    -   Output: The pattern with rewrites applied at every node once starting from the bottom.
    """
    return bottom_up(lambda p: rewriteWith(rule, p), pattern)


def replaceWith(rule, pattern):
    (ruleLHS, ruleRHS) = rule
    if ruleLHS == pattern:
        return ruleRHS
    return pattern


def replaceAnywhereWith(rule, pattern):
    return bottom_up(lambda p: replaceWith(rule, p), pattern)


def boolToMlPred(kast: KInner) -> KInner:
    return mlAnd([mlEqualsTrue(cond) for cond in flattenLabel('_andBool_', kast)])


def unsafeMlPredToBool(k):
    """Attempt to convert an ML Predicate back into a boolean expression.

    This is unsafe in general because not every ML Predicate can be represented correctly as a boolean expression.
    This function just makes a best-effort to do this.
    """
    if k is None:
        return None
    mlPredToBoolRules = [ (KApply('#Top')                                            , KToken('true'          , 'Bool'))                                # noqa
                        , (KApply('#Bottom')                                         , KToken('false'         , 'Bool'))                                # noqa
                        , (KApply('#And'     , [KVariable('#V1'), KVariable('#V2')]) , KApply('_andBool_'     , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                        , (KApply('#Or'      , [KVariable('#V1'), KVariable('#V2')]) , KApply('_orBool_'      , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                        , (KApply('#Not'     , [KVariable('#V1')])                   , KApply('notBool_'      , [KVariable('#V1')]))                    # noqa
                        , (KApply('#Equals'  , [KVariable('#V1'), KVariable('#V2')]) , KApply('_==K_'         , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                        , (KApply('#Implies' , [KVariable('#V1'), KVariable('#V2')]) , KApply('_impliesBool_' , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                        ]                                                                                                                               # noqa
    newK = k
    for rule in mlPredToBoolRules:
        newK = rewriteAnywhereWith(rule, newK)
    return newK


def simplifyBool(k):
    if k is None:
        return None
    simplifyRules = [ (KApply('_==K_', [KVariable('#LHS'), KToken('true', 'Bool')]), KVariable('#LHS'))                                                             # noqa
                    , (KApply('_==K_', [KToken('true', 'Bool'), KVariable('#RHS')]), KVariable('#RHS'))                                                             # noqa
                    , (KApply('_==K_', [KVariable('#LHS'), KToken('false', 'Bool')]), KApply('notBool_', [KVariable('#LHS')]))                                      # noqa
                    , (KApply('_==K_', [KToken('false', 'Bool'), KVariable('#RHS')]), KApply('notBool_', [KVariable('#RHS')]))                                      # noqa
                    , (KApply('notBool_', [KToken('false' , 'Bool')]), KToken('true'  , 'Bool'))                                                                    # noqa
                    , (KApply('notBool_', [KToken('true'  , 'Bool')]), KToken('false' , 'Bool'))                                                                    # noqa
                    , (KApply('notBool_', [KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')])]), KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('notBool_', [KApply('_=/=K_'   , [KVariable('#V1'), KVariable('#V2')])]), KApply('_==K_'    , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('notBool_', [KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')])]), KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('notBool_', [KApply('_=/=Int_' , [KVariable('#V1'), KVariable('#V2')])]), KApply('_==Int_'  , [KVariable('#V1'), KVariable('#V2')]))  # noqa
                    , (KApply('_andBool_', [KToken('true', 'Bool'), KVariable('#REST')]), KVariable('#REST'))                                                       # noqa
                    , (KApply('_andBool_', [KVariable('#REST'), KToken('true', 'Bool')]), KVariable('#REST'))                                                       # noqa
                    , (KApply('_andBool_', [KToken('false', 'Bool'), KVariable('#REST')]), KToken('false', 'Bool'))                                                 # noqa
                    , (KApply('_andBool_', [KVariable('#REST'), KToken('false', 'Bool')]), KToken('false', 'Bool'))                                                 # noqa
                    , (KApply('_orBool_', [KToken('false', 'Bool'), KVariable('#REST')]), KVariable('#REST'))                                                       # noqa
                    , (KApply('_orBool_', [KVariable('#REST'), KToken('false', 'Bool')]), KVariable('#REST'))                                                       # noqa
                    , (KApply('_orBool_', [KToken('true', 'Bool'), KVariable('#REST')]), KToken('true', 'Bool'))                                                    # noqa
                    , (KApply('_orBool_', [KVariable('#REST'), KToken('true', 'Bool')]), KToken('true', 'Bool'))                                                    # noqa
                    ]                                                                                                                                               # noqa
    newK = k
    for rule in simplifyRules:
        newK = rewriteAnywhereWith(rule, newK)
    return newK


def getOccurances(kast, pattern):
    occurances = []

    def addOccurance(k):
        if match(pattern, k):
            occurances.append(k)

    collect(addOccurance, kast)
    return occurances


def extract_lhs(term: KInner) -> KInner:
    return top_down(if_ktype(KRewrite, lambda rw: rw.lhs), term)


def extract_rhs(term: KInner) -> KInner:
    return top_down(if_ktype(KRewrite, lambda rw: rw.rhs), term)


def count_vars(term: KInner) -> Counter:
    counter: Counter = Counter()

    def count(term: KInner) -> None:
        if type(term) is KVariable:
            counter[term.name] += 1

    collect(count, term)
    return counter


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


def collectFreeVars(kast):
    return list(count_vars(kast).keys())


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


def splitConfigAndConstraints(kast):
    """Split the configuration/term from the constraints.

    -   Input: kast conjunct representing a constrained term.
    -   Output: tuple of term and constraint.
    """
    conjuncts = flattenLabel('#And', kast)
    term = None
    constraints = []
    for c in conjuncts:
        if type(c) is KApply and c.is_cell:
            term = c
        else:
            constraints.append(c)
    constraint = buildAssoc(mlTop(), '#And', constraints)
    return (term, constraint)


def propagateUpConstraints(k):
    """Try to propagate common constraints up disjuncts.

    -   Input: kast disjunct of constrained terms (conjuncts).
    -   Output: kast where common constraints in the disjunct have been propagated up.
    """
    def _propagateUpConstraints(_k):
        if not (type(_k) is KApply and _k.label == '#Or'):
            return _k
        conjuncts1 = flattenLabel('#And', _k.args[0])
        conjuncts2 = flattenLabel('#And', _k.args[1])
        (common1, l1, r1) = find_common_items(conjuncts1, conjuncts2)
        (common2, r2, l2) = find_common_items(r1, l1)
        common = common1 + common2
        if len(common) == 0:
            return _k
        conjunct1 = buildAssoc(mlTop(), '#And', l2)
        conjunct2 = buildAssoc(mlTop, '#And', r2)
        disjunct = KApply('#Or', [conjunct1, conjunct2])
        return buildAssoc(mlTop(), '#And', [disjunct] + common)
    return bottom_up(_propagateUpConstraints, k)


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
                config_var = _mkCellVar(k.label)
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


def pushDownRewrites(kast):
    """Traverse a term and push rewrites down as far as possible.

    -   Input: Kast term potentially with rewrites.
    -   Output: Kast term with rewrites localized (or removed) as much as possible.
    """
    def _pushDownRewrites(_kast):
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
                if lhs.items[0] == rhs.items[0]:
                    lowerRewrite = KRewrite(KSequence(lhs.items[1:]), KSequence(rhs.items[1:]))
                    return KSequence([lhs.items[0], lowerRewrite])
                if lhs.items[-1] == rhs.items[-1]:
                    lowerRewrite = KRewrite(KSequence(lhs.items[0:-1]), KSequence(rhs.items[0:-1]))
                    return KSequence([lowerRewrite, lhs.items[-1]])
            if type(lhs) is KSequence and lhs.arity > 0 and type(lhs.items[-1]) is KVariable and type(rhs) is KVariable and lhs.items[-1] == rhs:
                return KSequence([KRewrite(KSequence(lhs.items[0:-1]), KApply(klabelEmptyK)), rhs])
        return _kast
    return top_down(_pushDownRewrites, kast)


def inlineCellMaps(kast):
    """Ensure that cell map collections are printed nicely, not as Maps."

    -   Input: kast term.
    -   Output: kast term with cell maps inlined.
    """
    def _inlineCellMaps(_kast):
        if type(_kast) is KApply and _kast.label.endswith('CellMapItem'):
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
        if type(_kast) is KApply and _kast.arity == 1 and _kast.label.startswith('#SemanticCast'):
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
        if type(k) is KApply and k.is_cell and k.label in labels:
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


def minimizeTerm(term, keepVars=None, abstractLabels=[]):
    """Minimize a K term for pretty-printing.

    -   Input: kast term, and optionally requires and ensures clauses with constraints.
    -   Output: kast term minimized.
        -   Variables only used once will be removed.
        -   Unused cells will be abstracted.
        -   Attempt to remove useless conditions.
    """
    term = inlineCellMaps(term)
    term = removeSemanticCasts(term)
    term = uselessVarsToDots(term, keepVars=keepVars)
    term = labelsToDots(term, abstractLabels)
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

    ruleRequires = buildAssoc(KToken('true', 'Bool'), '_andBool_', dedupe(flattenLabel('_andBool_', ruleRequires)))
    ruleRequires = simplifyBool(ruleRequires)

    ruleEnsures = buildAssoc(KToken('true', 'Bool'), '_andBool_', dedupe(flattenLabel('_andBool_', ruleEnsures)))
    ruleEnsures = simplifyBool(ruleEnsures)

    constrainedVars = [] if keepVars is None else keepVars
    constrainedVars = constrainedVars + collectFreeVars(ruleRequires)
    constrainedVars = constrainedVars + collectFreeVars(ruleEnsures)
    ruleBody = minimizeTerm(ruleBody, keepVars=constrainedVars)

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
    rule = KApply('<generatedTop>', [KVariable('CONFIG'), KVariable('_')]), KVariable('CONFIG')
    return rewriteAnywhereWith(rule, term)


def isAnonVariable(kast):
    return type(kast) is KVariable and kast.name.startswith('_')


def omitLargeTokens(kast, maxLen=78):
    def _largeTokensToDots(_k):
        if type(_k) is KToken and len(_k.token) > maxLen:
            return KToken('...', _k.sort)
        return _k
    return bottom_up(_largeTokensToDots, kast)


def getCell(constrainedTerm, cellVariable):
    (state, _) = splitConfigAndConstraints(constrainedTerm)
    (_, subst) = splitConfigFrom(state)
    return subst[cellVariable]


def setCell(constrainedTerm, cellVariable, cellValue):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    (config, subst) = splitConfigFrom(state)
    subst[cellVariable] = cellValue
    return mlAnd([substitute(config, subst), constraint])


def structurallyFrameKCell(constrainedTerm):
    kCell = getCell(constrainedTerm, 'K_CELL')
    if type(kCell) is KSequence and kCell.arity > 0 and isAnonVariable(kCell.items[-1]):
        kCell = KSequence(kCell.items[0:-1] + (ktokenDots,))
    return setCell(constrainedTerm, 'K_CELL', kCell)


def applyCellSubst(constrainedTerm, cellSubst):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    (config, subst) = splitConfigFrom(state)
    for k in cellSubst:
        subst[k] = cellSubst[k]
    return KApply('#And', [substitute(config, subst), constraint])


def removeUselessConstraints(constrainedTerm, keepVars=None):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
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
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    constraint = removeConstraintClausesFor(varNames, constraint)
    return mlAnd([state, constraint])


def hasExistentials(pattern):
    return any([v.startswith('?') for v in collectFreeVars(pattern)])


def buildRule(ruleId, initConstrainedTerm, finalConstrainedTerm, claim=False, priority=None, keepVars=None) -> Tuple[KRuleLike, Dict[str, KVariable]]:
    (initConfig, initConstraint) = splitConfigAndConstraints(initConstrainedTerm)
    (finalConfig, finalConstraint) = splitConfigAndConstraints(finalConstrainedTerm)
    initConstraints = flattenLabel('#And', initConstraint)
    finalConstraints = [c for c in flattenLabel('#And', finalConstraint) if c not in initConstraints]
    initConstrainedTerm = mlAnd([initConfig] + initConstraints)
    finalConstrainedTerm = mlAnd([finalConfig] + finalConstraints)

    lhsVars = collectFreeVars(initConstrainedTerm)
    rhsVars = collectFreeVars(finalConstrainedTerm)
    varOccurances = count_vars(mlAnd([initConstrainedTerm, finalConstrainedTerm]))
    vSubst: Dict[str, KVariable] = {}
    vremapSubst: Dict[str, KVariable] = {}
    for v in varOccurances:
        newV = v
        if varOccurances[v] == 1:
            newV = '_' + newV
        if v in rhsVars and v not in lhsVars:
            newV = '?' + newV
        vSubst[v] = KVariable(newV)
        vremapSubst[newV] = KVariable(v)

    initConstrainedTerm = substitute(initConstrainedTerm, vSubst)
    finalConstrainedTerm = applyExistentialSubstitutions(substitute(finalConstrainedTerm, vSubst))
    (initConfig, initConstraint) = splitConfigAndConstraints(initConstrainedTerm)
    (finalConfig, finalConstraint) = splitConfigAndConstraints(finalConstrainedTerm)

    ruleBody = pushDownRewrites(KRewrite(initConfig, finalConfig))
    ruleRequires = simplifyBool(unsafeMlPredToBool(initConstraint))
    ruleEnsures = simplifyBool(unsafeMlPredToBool(finalConstraint))
    attDict = {} if claim or priority is None else {'priority': str(priority)}
    ruleAtt = KAtt(atts=attDict)

    rule: KRuleLike
    if not claim:
        rule = KRule(ruleBody, requires=ruleRequires, ensures=ruleEnsures, att=ruleAtt)
    else:
        rule = KClaim(ruleBody, requires=ruleRequires, ensures=ruleEnsures, att=ruleAtt)

    rule = rule.update_atts({'label': ruleId})
    newKeepVars = None
    if keepVars is not None:
        newKeepVars = [vSubst[v].name for v in keepVars]
    return (minimizeRule(rule, keepVars=newKeepVars), vremapSubst)


def onCells(cellHandler, constrainedTerm):
    """Given an effect and a constrained term, return the effect applied to the cells in the term.

    -   Input: Effect that takes as input a cell name and the contents of the cell, and a constrained term.
    -   Output: Constrained term with the effect applied to each cell.
    """
    (config, constraint) = splitConfigAndConstraints(constrainedTerm)
    constraints = flattenLabel('#And', constraint)
    (emptyConfig, subst) = splitConfigFrom(config)
    for k in subst:
        newCell = cellHandler(k, subst[k])
        if newCell is not None:
            (term, constraint) = newCell
            subst[k] = term
            if constraint not in constraints:
                constraints.append(constraint)
    return mlAnd([substitute(emptyConfig, subst)] + constraints)


def abstractTermSafely(kast, baseName='V'):
    vname = hash_str(kast)[0:8]
    return KVariable(baseName + '_' + vname)


def antiUnify(state1, state2):
    subst1 = {}
    subst2 = {}

    def _rewritesToAbstractions(_kast):
        if type(_kast) is KRewrite:
            return abstractTermSafely(_kast)
        return _kast

    minimizedRewrite = pushDownRewrites(KRewrite(state1, state2))
    abstractedState = bottom_up(_rewritesToAbstractions, minimizedRewrite)
    subst1 = match(abstractedState, state1)
    subst2 = match(abstractedState, state2)
    if subst1 is None or subst2 is None:
        fatal('Anti-unification failed to produce a more general state!')
    return (abstractedState, subst1, subst2)


def antiUnifyWithConstraints(constrainedTerm1, constrainedTerm2, implications=False, disjunct=False):
    (state1, constraint1) = splitConfigAndConstraints(constrainedTerm1)
    (state2, constraint2) = splitConfigAndConstraints(constrainedTerm2)
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
    clauses = [c for c in clauses if not (type(c) is KApply and c.label == '#Or')]
    constrainedTerm = mlAnd(clauses)
    return constrainedTerm


def abstractCell(constrainedTerm, cellName):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    constraints = flattenLabel('#And', constraint)
    cell = getCell(state, cellName)
    cellVar = KVariable(cellName)
    if type(cell) is not KVariable:
        state = setCell(state, cellName, cellVar)
        constraints.append(KApply('#Equals', [cellVar, cell]))
    return mlAnd([state] + constraints)


def applyExistentialSubstitutions(constrainedTerm):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    constraints = flattenLabel('#And', constraint)
    substPattern = mlEqualsTrue(KApply('_==K_', [KVariable('#VAR'), KVariable('#VAL')]))
    subst = {}
    newConstraints = []
    for c in constraints:
        substMatch = match(substPattern, c)
        if substMatch is not None and type(substMatch['#VAR']) is KVariable and substMatch['#VAR'].name.startswith('?'):
            subst[substMatch['#VAR'].name] = substMatch['#VAL']
        else:
            newConstraints.append(c)
    return substitute(mlAnd([state] + newConstraints), subst)


def constraintSubsume(constraint1, constraint2):
    if constraint1 == mlTop() or constraint1 == constraint2:
        return True
    elif type(constraint1) is KApply and constraint1.label == '#And':
        constraints1 = flattenLabel('#And', constraint1)
        if all([constraintSubsume(c, constraint2) for c in constraints1]):
            return True
    elif type(constraint1) is KApply and constraint1.label == '#Or':
        constraints1 = flattenLabel('#Or', constraint1)
        if any([constraintSubsume(c, constraint2) for c in constraints1]):
            return True
    elif type(constraint2) is KApply and constraint2.label == '#And':
        constraints2 = flattenLabel('#And', constraint2)
        if any([constraintSubsume(constraint1, c) for c in constraints2]):
            return True
    elif type(constraint2) is KApply and constraint2.label == '#Or':
        constraints2 = flattenLabel('#Or', constraint2)
        if all([constraintSubsume(constraint1, c) for c in constraints2]):
            return True
    else:
        return False


def matchWithConstraint(constrainedTerm1, constrainedTerm2):
    (state1, constraint1) = splitConfigAndConstraints(constrainedTerm1)
    (state2, constraint2) = splitConfigAndConstraints(constrainedTerm2)
    subst = match(state1, state2)
    if subst is not None and constraintSubsume(substitute(constraint1, subst), constraint2):
        return subst
    return None


def minimizeSubst(subst):
    return {k: subst[k] for k in subst if not (type(subst[k]) is KVariable and k == subst[k].name)}


def substToMlPred(subst):
    mlTerms = []
    for k in subst:
        if KVariable(k) != subst[k]:
            mlTerms.append(mlEquals(KVariable(k), subst[k]))
    return mlAnd(mlTerms)


def substToMap(subst):
    mapItems = [KApply('_|->_', [KVariable(k), subst[k]]) for k in subst]
    return buildAssoc(KApply('.Map'), '_Map_', mapItems)


def undoAliases(definition, kast):
    alias_undo_rewrites = [(sent.body.rhs, sent.body.lhs) for module in definition for sent in module if type(sent) is KRule and 'alias' in sent.att]
    newKast = kast
    for r in alias_undo_rewrites:
        newKast = rewriteAnywhereWith(r, newKast)
    return newKast
