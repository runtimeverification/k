from .cli_utils import fatal
from .kast import (
    KApply,
    KAs,
    KAtt,
    KBubble,
    KClaim,
    KConstant,
    KContext,
    KDefinition,
    KFlatModule,
    KProduction,
    KRewrite,
    KRule,
    KSequence,
    KSortSynonym,
    KSyntaxAssociativity,
    KSyntaxLexical,
    KSyntaxPriority,
    KSyntaxSort,
    KToken,
    KVariable,
    addAttributes,
    flattenLabel,
    getAttribute,
    isCellKLabel,
    isKApply,
    isKAs,
    isKAtt,
    isKBubble,
    isKClaim,
    isKContext,
    isKDefinition,
    isKFlatModule,
    isKProduction,
    isKRewrite,
    isKRule,
    isKSequence,
    isKSortSynonym,
    isKSyntaxAssociativity,
    isKSyntaxLexical,
    isKSyntaxPriority,
    isKSyntaxSort,
    isKToken,
    isKVariable,
    klabelEmptyK,
    ktokenDots,
)
from .prelude import (
    buildAssoc,
    mlAnd,
    mlEquals,
    mlEqualsTrue,
    mlImplies,
    mlOr,
    mlTop,
)
from .utils import combine_dicts, dedupe, find_common_items, hash_str


def match(pattern, kast):
    """Perform syntactic pattern matching and return the substitution.

    -   Input: a pattern and a kast term.
    -   Output: substitution instantiating the pattern to the kast term.
    """
    subst = {}
    if isKVariable(pattern):
        return {pattern["name"]: kast}
    if isKToken(pattern) and isKToken(kast):
        return {} if pattern["token"] == kast["token"] else None
    if isKApply(pattern) and isKApply(kast) \
            and pattern["label"] == kast["label"] and len(pattern["args"]) == len(kast["args"]):
        for (patternArg, kastArg) in zip(pattern["args"], kast["args"]):
            argSubst = match(patternArg, kastArg)
            subst = combine_dicts(subst, argSubst)
            if subst is None:
                return None
        return subst
    if isKRewrite(pattern) and isKRewrite(kast):
        lhsSubst = match(pattern['lhs'], kast['lhs'])
        rhsSubst = match(pattern['rhs'], kast['rhs'])
        return combine_dicts(lhsSubst, rhsSubst)
    if isKSequence(pattern) and isKSequence(kast) and len(pattern['items']) == len(kast['items']):
        for (patternItem, substItem) in zip(pattern['items'], kast['items']):
            itemSubst = match(patternItem, substItem)
            subst = combine_dicts(subst, itemSubst)
            if subst is None:
                return None
        return subst
    return None


def onChildren(kast, effect):
    if isKApply(kast):
        return KApply(kast['label'], [effect(arg) for arg in kast['args']])
    elif isKRewrite(kast):
        return KRewrite(effect(kast['lhs']), effect(kast['rhs']))
    elif isKSequence(kast):
        return KSequence([effect(item) for item in kast['items']])
    return kast


def traverseBottomUp(kast, effect):
    return effect(onChildren(kast, lambda _kast: traverseBottomUp(_kast, effect)))


def traverseTopDown(kast, effect):
    return onChildren(effect(kast), lambda _kast: traverseTopDown(_kast, effect))


def collectBottomUp(kast, callback):
    callback(onChildren(kast, lambda _kast: collectBottomUp(_kast, callback)))


def substitute(pattern, substitution):
    """Apply a substitution to a pattern.

    -   Input: a pattern with free variables and a substitution.
    -   Output: the pattern with the substitution applied.
    """
    def replace(k):
        if isKVariable(k) and k["name"] in substitution:
            return substitution[k["name"]]
        return k
    return traverseBottomUp(pattern, replace)


def whereMatchingBottomUp(effect, matchPattern, pattern):
    def _effect(k):
        matchingSubst = match(matchPattern, k)
        newK = k
        if matchingSubst is not None:
            newK = effect(matchingSubst)
        return newK
    return traverseBottomUp(_effect, pattern)


def replaceKLabels(pattern, klabelMap):
    def replace(k):
        if isKApply(k) and k["label"] in klabelMap:
            return KApply(klabelMap[k["label"]], k["args"])
        return k
    return traverseBottomUp(pattern, replace)


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
    return traverseBottomUp(pattern, lambda p: rewriteWith(rule, p))


def replaceWith(rule, pattern):
    (ruleLHS, ruleRHS) = rule
    if ruleLHS == pattern:
        return ruleRHS
    return pattern


def replaceAnywhereWith(rule, pattern):
    return traverseBottomUp(pattern, lambda p: replaceWith(rule, p))


def unsafeMlPredToBool(k):
    """Attempt to convert an ML Predicate back into a boolean expression.

    This is unsafe in general because not every ML Predicate can be represented correctly as a boolean expression.
    This function just makes a best-effort to do this.
    """
    if k is None:
        return None
    mlPredToBoolRules = [ (KApply('#Top'     , [])                                   , KToken('true'          , 'Bool'))                                # noqa
                        , (KApply('#Bottom'  , [])                                   , KToken('false'         , 'Bool'))                                # noqa
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

    collectBottomUp(kast, addOccurance)
    return occurances


def countVarOccurances(kast, numOccurances=None):
    """Count the number of occurances of each variable in a proof.

    -   Input: Kast term.
    -   Output: Map of variable names to their number of occurances.
    """
    numOccurances = {} if numOccurances is None else numOccurances

    def _getNumOccurances(_kast):
        if isKVariable(_kast):
            vName = _kast['name']
            if vName in numOccurances:
                numOccurances[vName] += 1
            else:
                numOccurances[vName] = 1

    collectBottomUp(kast, _getNumOccurances)
    return numOccurances


def collectFreeVars(kast):
    return list(countVarOccurances(kast).keys())


def splitConfigAndConstraints(kast):
    """Split the configuration/term from the constraints.

    -   Input: kast conjunct representing a constrained term.
    -   Output: tuple of term and constraint.
    """
    conjuncts = flattenLabel('#And', kast)
    term = None
    constraints = []
    for c in conjuncts:
        if isKApply(c) and isCellKLabel(c['label']):
            term = c
        else:
            constraints.append(c)
    constraint = buildAssoc(KConstant('#Top'), '#And', constraints)
    return (term, constraint)


def propagateUpConstraints(k):
    """Try to propagate common constraints up disjuncts.

    -   Input: kast disjunct of constrained terms (conjuncts).
    -   Output: kast where common constraints in the disjunct have been propagated up.
    """
    def _propagateUpConstraints(_k):
        if not (isKApply(_k) and _k['label'] == '#Or'):
            return _k
        conjuncts1 = flattenLabel('#And', _k['args'][0])
        conjuncts2 = flattenLabel('#And', _k['args'][1])
        (common1, l1, r1) = find_common_items(conjuncts1, conjuncts2)
        (common2, r2, l2) = find_common_items(r1, l1)
        common = common1 + common2
        if len(common) == 0:
            return _k
        conjunct1 = buildAssoc(KConstant('#Top'), '#And', l2)
        conjunct2 = buildAssoc(KConstant('#Top'), '#And', r2)
        disjunct = KApply('#Or', [conjunct1, conjunct2])
        return buildAssoc(KConstant('#Top'), '#And', [disjunct] + common)
    return traverseBottomUp(k, _propagateUpConstraints)


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
        if isKApply(k) and isCellKLabel(k['label']):
            if len(k['args']) == 1 and not (isKApply(k['args'][0]) and isCellKLabel(k['args'][0]['label'])):
                config_var = _mkCellVar(k['label'])
                initial_substitution[config_var] = k['args'][0]
                return KApply(k['label'], [KVariable(config_var)])
        return k

    symbolic_config = traverseTopDown(configuration, _replaceWithVar)
    return (symbolic_config, initial_substitution)


def collapseDots(kast):
    """Given a configuration with structural frames `...`, minimize the structural frames needed.

    -   Input: a configuration, potentially with structural frames.
    -   Output: the same configuration, with the amount of structural framing minimized.
    """
    def _collapseDots(_kast):
        if isKApply(_kast):
            label = _kast['label']
            args = _kast['args']
            if isCellKLabel(label) and len(args) == 1 and args[0] == ktokenDots:
                return ktokenDots
            newArgs = [arg for arg in args if arg != ktokenDots]
            if isCellKLabel(label) and len(newArgs) == 0:
                return ktokenDots
            if len(newArgs) < len(args):
                newArgs.append(ktokenDots)
            return KApply(label, newArgs)
        elif isKRewrite(_kast):
            if _kast['lhs'] == ktokenDots:
                return ktokenDots
        return _kast
    return traverseBottomUp(kast, _collapseDots)


def pushDownRewrites(kast):
    """Traverse a term and push rewrites down as far as possible.

    -   Input: Kast term potentially with rewrites.
    -   Output: Kast term with rewrites localized (or removed) as much as possible.
    """
    def _pushDownRewrites(_kast):
        if isKRewrite(_kast):
            lhs = _kast['lhs']
            rhs = _kast['rhs']
            if lhs == rhs:
                return lhs
            if isKVariable(lhs) and isKVariable(rhs) and lhs['name'] == rhs['name']:
                return lhs
            if isKApply(lhs) and isKApply(rhs) and lhs['label'] == rhs['label'] and len(lhs['args']) == len(rhs['args']):
                newArgs = [KRewrite(lArg, rArg) for (lArg, rArg) in zip(lhs['args'], rhs['args'])]
                return KApply(lhs['label'], newArgs)
            if isKSequence(lhs) and isKSequence(rhs) and len(lhs['items']) > 0 and len(rhs['items']) > 0:
                if lhs['items'][0] == rhs['items'][0]:
                    lowerRewrite = KRewrite(KSequence(lhs['items'][1:]), KSequence(rhs['items'][1:]))
                    return KSequence([lhs['items'][0], lowerRewrite])
                if lhs['items'][-1] == rhs['items'][-1]:
                    lowerRewrite = KRewrite(KSequence(lhs['items'][0:-1]), KSequence(rhs['items'][0:-1]))
                    return KSequence([lowerRewrite, lhs['items'][-1]])
            if isKSequence(lhs) and len(lhs['items']) > 0 and isKVariable(lhs['items'][-1]) and isKVariable(rhs) and lhs['items'][-1] == rhs:
                return KSequence([KRewrite(KSequence(lhs['items'][0:-1]), KConstant(klabelEmptyK)), rhs])
        return _kast
    return traverseTopDown(kast, _pushDownRewrites)


def inlineCellMaps(kast):
    """Ensure that cell map collections are printed nicely, not as Maps."

    -   Input: kast term.
    -   Output: kast term with cell maps inlined.
    """
    def _inlineCellMaps(_kast):
        if isKApply(_kast) and _kast["label"].endswith('CellMapItem'):
            mapKey = _kast["args"][0]
            if isKApply(mapKey) and isCellKLabel(mapKey["label"]):
                return _kast["args"][1]
        return _kast
    return traverseBottomUp(kast, _inlineCellMaps)


def removeSemanticCasts(kast):
    """Remove injected `#SemanticCast*` nodes in AST.

    -   Input: kast (possibly) containing automatically injected `#SemanticCast*` KApply nodes.
    -   Output: kast without the `#SemanticCast*` nodes.
    """
    def _removeSemanticCasts(_kast):
        if isKApply(_kast) and len(_kast['args']) == 1 and _kast['label'].startswith('#SemanticCast'):
            return _kast['args'][0]
        return _kast
    return traverseBottomUp(kast, _removeSemanticCasts)


def markUselessVars(kast):
    """Given a kast term as input with variables, return one where the useless vars are appropriately marked.

    -   Input: A Kast term.
    -   Output: Kast term with variables appropriately named.
    """
    occurances = countVarOccurances(kast)
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
    initList = {}
    if keepVars is not None:
        for v in keepVars:
            if v not in initList:
                initList[v] = 1
            else:
                initList[v] += 1
    numOccurances = countVarOccurances(kast, numOccurances=initList)

    def _collapseUselessVars(_kast):
        if isKApply(_kast) and isCellKLabel(_kast['label']):
            newArgs = []
            for arg in _kast['args']:
                if isKVariable(arg) and numOccurances[arg['name']] == 1:
                    newArgs.append(ktokenDots)
                else:
                    newArgs.append(arg)
            return KApply(_kast['label'], newArgs)
        return _kast

    return traverseBottomUp(kast, _collapseUselessVars)


def labelsToDots(kast, labels):
    """Abstract specific labels for printing.

    -   Input: kast term, and list of labels to abstract.
    -   Output: kast term with those labels abstracted.
    """
    def _labelstoDots(k):
        if isKApply(k) and isCellKLabel(k['label']) and k['label'] in labels:
            return ktokenDots
        return k
    return traverseBottomUp(kast, _labelstoDots)


def onAttributes(kast, effect):
    if isKAs(kast):
        return KAs(kast['pattern'], kast['alias'], att=effect(kast['att']))
    elif isKRule(kast):
        return KRule(kast['body'], requires=kast['requires'], ensures=kast['ensures'], att=effect(kast['att']))
    elif isKClaim(kast):
        return KClaim(kast['body'], requires=kast['requires'], ensures=kast['ensures'], att=effect(kast['att']))
    elif isKContext(kast):
        return KContext(kast['body'], requires=kast['requires'], att=effect(kast['att']))
    elif isKBubble(kast):
        return KBubble(kast['sentenceType'], kast['contents'], att=effect(kast['att']))
    elif isKProduction(kast):
        return KProduction(kast['productionItems'], kast['sort'], att=effect(kast['att']))
    elif isKSyntaxAssociativity(kast):
        return KSyntaxAssociativity(kast['assoc'], tags=kast['tags'], att=effect(kast['att']))
    elif isKSyntaxPriority(kast):
        return KSyntaxPriority(priorities=kast['priorities'], att=effect(kast['att']))
    elif isKSyntaxSort(kast):
        return KSyntaxSort(kast['sort'], att=effect(kast['att']))
    elif isKSortSynonym(kast):
        return KSortSynonym(kast['newSort'], kast['oldSort'], att=effect(kast['att']))
    elif isKSyntaxLexical(kast):
        return KSyntaxLexical(kast['name'], kast['regex'], att=effect(kast['att']))
    elif isKFlatModule(kast):
        localSentences = [onAttributes(sent, effect) for sent in kast['localSentences']]
        return KFlatModule(kast['name'], kast['imports'], localSentences, att=effect(kast['att']))
    elif isKDefinition(kast):
        modules = [onAttributes(mod, effect) for mod in kast['modules']]
        requires = None if 'requires' not in kast else kast['requires']
        return KDefinition(kast['mainModule'], modules, requires=requires, att=effect(kast['att']))
    fatal('No attributes for: ' + kast['node'] + '.')


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
    if not (isKRule(rule) or isKClaim(rule)):
        return rule

    ruleBody = rule['body']
    ruleRequires = rule['requires']
    ruleEnsures = rule['ensures']
    ruleAtts = rule['att']

    if ruleRequires is not None:
        ruleRequires = buildAssoc(KToken('true', 'Bool'), '_andBool_', dedupe(flattenLabel('_andBool_', ruleRequires)))
        ruleRequires = simplifyBool(ruleRequires)

    if ruleEnsures is not None:
        ruleEnsures = buildAssoc(KToken('true', 'Bool'), '_andBool_', dedupe(flattenLabel('_andBool_', ruleEnsures)))
        ruleEnsures = simplifyBool(ruleEnsures)

    ruleRequires = None if ruleRequires == KToken('true', 'Bool') else ruleRequires
    ruleEnsures = None if ruleEnsures == KToken('true', 'Bool') else ruleEnsures

    constrainedVars = [] if keepVars is None else keepVars
    if ruleRequires is not None:
        constrainedVars = constrainedVars + collectFreeVars(ruleRequires)
    if ruleEnsures is not None:
        constrainedVars = constrainedVars + collectFreeVars(ruleEnsures)
    ruleBody = minimizeTerm(ruleBody, keepVars=constrainedVars)

    if ruleRequires == KToken('true', 'Bool'):
        ruleRequires = None
    if isKRule(rule):
        return KRule(ruleBody, requires=ruleRequires, ensures=ruleEnsures, att=ruleAtts)
    else:
        return KClaim(ruleBody, requires=ruleRequires, ensures=ruleEnsures, att=ruleAtts)


def removeSourceMap(k):
    """Remove source map information from a given definition.

    Input: A JSON encoded K object.
    Output: The same JSON encoded object, with all source information stripped.
    """
    def _removeSourceMap(att):
        if isKAtt(att):
            atts = att['att']
            newAtts = {}
            for attKey in atts.keys():
                if attKey != 'org.kframework.attributes.Source' and attKey != 'org.kframework.attributes.Location':
                    newAtts[attKey] = atts[attKey]
            return KAtt(atts=newAtts)
    return onAttributes(k, _removeSourceMap)


def removeGeneratedCells(constrainedTerm):
    """Remove <generatedTop> and <generatedCounter> from a configuration.

    -   Input: Constrained term which contains <generatedTop> and <generatedCounter>.
    -   Output: Constrained term with those cells removed.
    """
    rule = KApply('<generatedTop>', [KVariable('CONFIG'), KApply('<generatedCounter>', [KVariable('_')])]), KVariable('CONFIG')
    return rewriteAnywhereWith(rule, constrainedTerm)


def isAnonVariable(kast):
    return isKVariable(kast) and kast['name'].startswith('_')


def omitLargeTokens(kast, maxLen=78):
    def _largeTokensToDots(_k):
        if isKToken(_k) and len(_k['token']) > maxLen:
            return KToken('...', _k['sort'])
        return _k
    return traverseBottomUp(kast, _largeTokensToDots)


def getCell(constrainedTerm, cellVariable):
    (state, _) = splitConfigAndConstraints(constrainedTerm)
    (_, subst) = splitConfigFrom(state)
    return subst[cellVariable]


def setCell(constrainedTerm, cellVariable, cellValue):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    (config, subst) = splitConfigFrom(state)
    subst[cellVariable] = cellValue
    return KApply('#And', [substitute(config, subst), constraint])


def structurallyFrameKCell(constrainedTerm):
    kCell = getCell(constrainedTerm, 'K_CELL')
    if isKSequence(kCell) and len(kCell['items']) > 0 and isAnonVariable(kCell['items'][-1]):
        kCell = KSequence(kCell['items'][0:-1] + [ktokenDots])
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


def buildRule(ruleId, initConstrainedTerm, finalConstrainedTerm, claim=False, priority=None, keepVars=None):
    (initConfig, initConstraint) = splitConfigAndConstraints(initConstrainedTerm)
    (finalConfig, finalConstraint) = splitConfigAndConstraints(finalConstrainedTerm)
    initConstraints = flattenLabel('#And', initConstraint)
    finalConstraints = [c for c in flattenLabel('#And', finalConstraint) if c not in initConstraints]
    initConstrainedTerm = mlAnd([initConfig] + initConstraints)
    finalConstrainedTerm = mlAnd([finalConfig] + finalConstraints)

    lhsVars = collectFreeVars(initConstrainedTerm)
    rhsVars = collectFreeVars(finalConstrainedTerm)
    varOccurances = countVarOccurances(mlAnd([initConstrainedTerm, finalConstrainedTerm]))
    vSubst = {}
    vremapSubst = {}
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
    ruleAtt = None if claim or priority is None else KAtt(atts={'priority': str(priority)})
    if not claim:
        rule = KRule(ruleBody, requires=ruleRequires, ensures=ruleEnsures, att=ruleAtt)
    else:
        rule = KClaim(ruleBody, requires=ruleRequires, ensures=ruleEnsures, att=ruleAtt)
    rule = addAttributes(rule, {'label': ruleId})
    newKeepVars = None
    if keepVars is not None:
        newKeepVars = [vSubst[v]['name'] for v in keepVars]
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
        if isKRewrite(_kast):
            return abstractTermSafely(_kast)
        return _kast

    minimizedRewrite = pushDownRewrites(KRewrite(state1, state2))
    abstractedState = traverseBottomUp(minimizedRewrite, _rewritesToAbstractions)
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


def removeDisjuncts(constrainedTerm):
    clauses = flattenLabel('#And', constrainedTerm)
    clauses = [c for c in clauses if not (isKApply(c) and c['label'] == '#Or')]
    constrainedTerm = mlAnd(clauses)
    return constrainedTerm


def abstractCell(constrainedTerm, cellName):
    (state, constraint) = splitConfigAndConstraints(constrainedTerm)
    constraints = flattenLabel('#And', constraint)
    cell = getCell(state, cellName)
    cellVar = KVariable(cellName)
    if not isKVariable(cell):
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
        if substMatch is not None and isKVariable(substMatch['#VAR']) and substMatch['#VAR']['name'].startswith('?'):
            subst[substMatch['#VAR']['name']] = substMatch['#VAL']
        else:
            newConstraints.append(c)
    return substitute(mlAnd([state] + newConstraints), subst)


def constraintSubsume(constraint1, constraint2):
    if constraint1 == mlTop() or constraint1 == constraint2:
        return True
    elif isKApply(constraint1) and constraint1['label'] == '#And':
        constraints1 = flattenLabel('#And', constraint1)
        if all([constraintSubsume(c, constraint2) for c in constraints1]):
            return True
    elif isKApply(constraint1) and constraint1['label'] == '#Or':
        constraints1 = flattenLabel('#Or', constraint1)
        if any([constraintSubsume(c, constraint2) for c in constraints1]):
            return True
    elif isKApply(constraint2) and constraint2['label'] == '#And':
        constraints2 = flattenLabel('#And', constraint2)
        if any([constraintSubsume(constraint1, c) for c in constraints2]):
            return True
    elif isKApply(constraint2) and constraint2['label'] == '#Or':
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
    return {k: subst[k] for k in subst if not (isKVariable(subst[k]) and k == subst[k]['name'])}


def substToMlPred(subst):
    mlTerms = []
    for k in subst:
        if KVariable(k) != subst[k]:
            mlTerms.append(mlEquals(KVariable(k), subst[k]))
    return mlAnd(mlTerms)


def substToMap(subst):
    mapItems = [KApply('_|->_', [KVariable(k), subst[k]]) for k in subst]
    return buildAssoc(KConstant('.Map'), '_Map_', mapItems)


def undoAliases(definition, kast):
    alias_undo_rewrites = [(sent['body']['rhs'], sent['body']['lhs']) for module in definition['modules'] for sent in module['localSentences'] if isKRule(sent) and getAttribute(sent, 'alias') is not None]
    newKast = kast
    for r in alias_undo_rewrites:
        newKast = rewriteAnywhereWith(r, newKast)
    return newKast
