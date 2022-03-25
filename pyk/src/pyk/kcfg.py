import json
import threading
from typing import Final

from graphviz import Digraph

from .cli_utils import fatal, notif
from .kast import KClaim, KFlatModule, KImport, KInner, KRule
from .kastManip import (
    buildRule,
    matchWithConstraint,
    minimizeSubst,
    mlAnd,
    simplifyBool,
    substitute,
    substToMap,
    unsafeMlPredToBool,
)
from .utils import compare_short_hashes, hash_str, shorten_hashes


class KCFG:
    _FIELDS: Final = (
        'states',
        'graph',
        'abstractions',
        'loop',
        'split',
        'init',
        'target',
        'terminal',
        'stuck',
        'subsumptions',
        'frontier',
    )

    _NODE_ATTRS: Final = ('init', 'target', 'stuck', 'terminal', 'frontier', 'loop', 'split')

    def __init__(self):
        # todo: switch to sets instead of lists everywhere
        # where it is possible
        # and make encoders/decoders for that
        # it is  preparation for immutable data structures
        # for parallel execution
        self.states = {}
        self.graph = {}
        self.abstractions = {}
        self.loop = []
        self.split = []
        self.init = []
        self.target = []
        self.terminal = []
        self.stuck = []
        self.subsumptions = {}
        self.frontier = []
        self._lock = threading.RLock()

    def __enter__(self):
        self._lock.acquire()
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self._lock.release()
        if exc_type is None:
            return True
        return False

    @staticmethod
    def _encode(value):
        result = None
        if type(value) is dict:
            result = {}
            for (key, val) in value.items():
                result[key] = KCFG._encode(val)
        elif type(value) is set:
            result = {'__kcfg_type__': 'set'}
            val = []
            for item in value:
                val.append(KCFG._encode(item))
            result['__kcfg_set_items__'] = val
        elif isinstance(value, KInner):
            result = value.to_dict()
            result['__kcfg_type__'] = 'k'
        else:
            result = value
        return result

    @staticmethod
    def _decode(value):
        result = None
        if type(value) is dict:
            if '__kcfg_type__' in value and value['__kcfg_type__'] == 'set':
                items = value['__kcfg_set_items__']
                result = set()
                for item in items:
                    result.add(KCFG._decode(item))
            elif '__kcfg_type__' in value and value['__kcfg_type__'] == 'k':
                return KInner.from_dict(value)
            else:
                result = {}
                for (key, val) in value.items():
                    result[key] = KCFG._decode(val)
        else:
            result = value
        return result

    def _assign(self, other):
        self.states = other.states
        self.graph = other.graph
        self.abstractions = other.abstractions
        self.loop = other.loop
        self.split = other.split
        self.init = other.init
        self.target = other.target
        self.terminal = other.terminal
        self.stuck = other.stuck
        self.subsumptions = other.subsumptions
        self.frontier = other.frontier

    def to_dict(self):
        dct = {}
        for field in KCFG._FIELDS:
            dct[field] = getattr(self, field)
        return KCFG._encode(dct)

    @staticmethod
    def from_dict(dct):
        dct = KCFG._decode(dct)
        cfg = KCFG()
        for field in KCFG._FIELDS:
            if field in dct:
                setattr(cfg, field, dct[field])
        return cfg

    def to_json(self):
        return json.dumps(self.to_dict(), sort_keys=True)

    @staticmethod
    def from_json(s: str) -> 'KCFG':
        return KCFG.from_dict(json.loads(s))

    def to_dot(self, kprint):
        graph = Digraph()

        def _short_label(_label):
            return '\n'.join([label_line if len(label_line) < 100 else (label_line[0:100] + ' ...') for label_line in _label.split('\n')])

        for state in self.states:
            classAttrs = ' '.join(self.getNodeAttributes(state))
            label = shorten_hashes(state) + (classAttrs and ' ' + classAttrs)
            attrs = {'class': classAttrs} if classAttrs else {}
            graph.node(name=state, label=label, **attrs)
        for source in self.graph:
            for target in self.graph[source]:
                edge = self.graph[source][target]
                display_condition = simplifyBool(unsafeMlPredToBool(edge['condition']))
                depth = edge['depth']
                classes = edge['classes']
                label = '\nandBool'.join(kprint.prettyPrint(display_condition).split(' andBool'))
                label = f'{label}\n{depth} steps'
                label = _short_label(label)
                classAttrs = ' '.join(classes)
                attrs = {'class': classAttrs} if classAttrs else {}
                graph.edge(tail_name=source, head_name=target, label=f'  {label}        ', **attrs)
        for state in self.abstractions:
            for abstractId in self.abstractions[state]:
                subst = substToMap(minimizeSubst(self.subsumptions[state][abstractId]))
                label = kprint.prettyPrint(subst)
                label = _short_label(label)
                attrs = {'class': 'abstraction', 'style': 'dashed'}
                graph.edge(tail_name=state, head_name=abstractId, label=f'  {label}        ', **attrs)
        for target in self.target:
            for node in self.frontier:
                attrs = {'class': 'target', 'style': 'solid'}
                graph.edge(tail_name=node, head_name=target, label='  ???', **attrs)
            for node in self.terminal:
                attrs = {'class': 'target', 'style': 'dashed'}
                graph.edge(tail_name=node, head_name=target, label='  ???', **attrs)
        return graph.source

    def getNodeAttributes(self, nodeId):
        atts = []
        for att in KCFG._NODE_ATTRS:
            if nodeId in self.__getattribute__(att):
                atts.append(att)
        return atts

    def getTermHash(self, term):
        return hash_str(term.to_json())

    def getStateIdByShortHash(self, shortHash):
        for h in self.states:
            if compare_short_hashes(shortHash, h):
                return h
        return None

    def getNodesByHashes(self, shortHashes):
        return [self.getStateIdByShortHash(h) for h in shortHashes]

    def insertNode(self, newConstrainedTerm):
        subsumes = []
        subsumedBy = []
        for constrainedTermId in self.states:
            constrainedTerm = self.states[constrainedTermId]
            subsumedWith = matchWithConstraint(constrainedTerm, newConstrainedTerm)
            subsumesWith = matchWithConstraint(newConstrainedTerm, constrainedTerm)
            if subsumedWith is not None and subsumesWith is not None:
                return (False, constrainedTermId)
            elif subsumedWith is not None:
                subsumedBy.append((constrainedTermId, subsumedWith))
            elif subsumesWith is not None:
                subsumes.append((constrainedTermId, subsumesWith))
        newConstrainedTermId = self.getTermHash(newConstrainedTerm)
        self.states[newConstrainedTermId] = newConstrainedTerm
        self.graph[newConstrainedTermId] = {}
        self.subsumptions[newConstrainedTermId] = {}
        self.abstractions[newConstrainedTermId] = []

        for (ctid, subst) in subsumes:
            self.subsumptions[ctid][newConstrainedTermId] = subst
        for (ctid, subst) in subsumedBy:
            self.subsumptions[newConstrainedTermId][ctid] = subst

        return (True, newConstrainedTermId)

    def insertAbstraction(self, concreteId, abstractId):
        if concreteId == abstractId:
            return self
        if abstractId not in self.getMoreGeneralNodes(concreteId):
            fatal('Node ' + str(abstractId) + ' does not abstract node ' + str(concreteId) + ' as claimed.')
        if abstractId not in self.abstractions[concreteId]:
            self.abstractions[concreteId].append(abstractId)
        return self

    # heavy
    def removeNode(self, nodeId):
        if nodeId not in self.states:
            raise ValueError(f'Unknown node: {nodeId}')

        self.states.pop(nodeId)
        if nodeId in self.frontier:
            for nid in (self.getConcretizations(nodeId) + self.getPredecessors(nodeId)):
                if nid not in self.frontier:
                    self.frontier.append(nid)
        for k in ['subsumptions', 'graph']:
            self.__getattribute__(k).pop(nodeId, None)
            for initNode in self.__getattribute__(k):
                if nodeId in self.__getattribute__(k)[initNode]:
                    self.__getattribute__(k)[initNode].pop(nodeId)
        for k in ['abstractions']:
            self.__getattribute__(k).pop(nodeId, None)
            for initNode in self.__getattribute__(k):
                self.__getattribute__(k)[initNode] = [n for n in self.__getattribute__(k)[initNode] if n != nodeId]
        for k in KCFG._NODE_ATTRS:
            self.__setattr__(k, [n for n in self.__getattribute__(k) if n != nodeId])

    def getMoreGeneralNodes(self, nodeId):
        if nodeId not in self.subsumptions:
            return []
        return list(self.subsumptions[nodeId].keys())

    # heavy
    def getLessGeneralNodes(self, nodeId):
        return [nid for nid in self.subsumptions if nodeId in self.getMoreGeneralNodes(nid)]

    def getAbstractions(self, nodeId):
        if nodeId not in self.abstractions:
            return []
        return self.abstractions[nodeId]

    # heavy
    def getConcretizations(self, nodeId):
        return [nid for nid in self.abstractions if nodeId in self.getAbstractions(nid)]

    def getSuccessors(self, nodeId):
        if nodeId not in self.graph:
            return []
        return list(self.graph[nodeId].keys())

    # heavy
    def getPredecessors(self, nodeId):
        return [nid for nid in self.graph if nodeId in self.getSuccessors(nid)]

    def getEdges(self):
        return [(s, f) for s in self.graph for f in self.graph[s]]

    def insertEdge(self, initConstrainedTermId, condition, finalConstrainedTermId, depth, classes=[], priority=50):
        edgeLabel = {'depth': depth, 'condition': condition, 'classes': [c for c in classes], 'priority': priority}
        if finalConstrainedTermId in self.graph[initConstrainedTermId] and self.graph[initConstrainedTermId][finalConstrainedTermId] == edgeLabel:
            return self
        self.graph[initConstrainedTermId][finalConstrainedTermId] = edgeLabel

        predNodes = self.transitiveClosureFromState(initConstrainedTermId, reverse=True)
        moreGeneralNodes = self.getMoreGeneralNodes(finalConstrainedTermId)
        for nid in predNodes:
            if nid in moreGeneralNodes:
                if nid not in self.getAbstractions(finalConstrainedTermId):
                    self.abstractions[finalConstrainedTermId].append(nid)
                if depth == 0 and nid == initConstrainedTermId and finalConstrainedTermId not in self.split:
                    self.split.append(finalConstrainedTermId)
                elif nid not in self.loop:
                    self.loop.append(nid)

        return self

    def getEdgeCondition(self, initNodeId, finalNodeId):
        return self.graph[initNodeId][finalNodeId]['condition']

    def getEdgeSentence(self, initNodeId, finalNodeId, priority=50):
        sentenceId = 'BASIC-BLOCK-' + str(initNodeId) + '-TO-' + str(finalNodeId)
        initConstrainedTerm = self.states[initNodeId]
        finalConstrainedTerm = self.states[finalNodeId]
        edge = self.graph[initNodeId][finalNodeId]
        verified = 'verified' in edge['classes']
        edgeConstraint = edge['condition']
        initConstrainedTerm = mlAnd([initConstrainedTerm, edgeConstraint])
        return buildRule(sentenceId, initConstrainedTerm, finalConstrainedTerm, claim=not verified, priority=priority)

    def getModule(self, moduleName, mainModuleName, rules=False, priority=50):
        newSentences = []
        for i in self.graph:
            for j in self.graph[i]:
                (newSentence, _) = self.getEdgeSentence(i, j, priority=priority)
                if (rules and type(newSentence) is KRule) or (not rules and type(newSentence) is KClaim):
                    newSentences.append(newSentence)
        return KFlatModule(moduleName, [KImport(mainModuleName)], newSentences)

    def markEdgeVerified(self, initConstrainedTermId, finalConstrainedTermId):
        self.graph[initConstrainedTermId][finalConstrainedTermId]['classes'].append('verified')

    def markEdgeAsyncProcess(self, initConstrainedTermId, finalConstrainedTermId):
        self.graph[initConstrainedTermId][finalConstrainedTermId]['classes'].append('async_processed')

    def clearEdgeMarkAsyncProcess(self, initConstrainedTermId, finalConstrainedTermId):
        self.graph[initConstrainedTermId][finalConstrainedTermId]['classes'].remove('async_processed')

    def transitiveClosureFromState(self, constrainedTermId, reverse=False, stopAtLoops=False, stopAtNodes=None):
        constrainedTermIds = []
        newConstrainedTermIds = [constrainedTermId]
        stopNodes = [] if not stopAtLoops else self.loop
        if stopAtNodes is not None:
            stopNodes.extend(stopAtNodes)
        while len(newConstrainedTermIds) > 0:
            constrainedTermId = newConstrainedTermIds.pop(0)
            if constrainedTermId not in constrainedTermIds:
                constrainedTermIds.append(constrainedTermId)
                if constrainedTermId not in stopNodes:
                    if not reverse:
                        newConstrainedTermIds.extend(self.getSuccessors(constrainedTermId))
                        newConstrainedTermIds.extend(self.getAbstractions(constrainedTermId))
                    else:
                        newConstrainedTermIds.extend(self.getPredecessors(constrainedTermId))
                        newConstrainedTermIds.extend(self.getConcretizations(constrainedTermId))
        return constrainedTermIds

    def nonLoopingPathsBetweenStates(self, initConstrainedTermId, finalConstrainedTermId):
        paths = []
        worklistPaths = [[initConstrainedTermId]]
        while len(worklistPaths) > 0:
            nextPath = worklistPaths.pop(0)
            if nextPath[-1] == finalConstrainedTermId:
                paths.append(nextPath)
            else:
                initState = nextPath[-1]
                for s in (self.getSuccessors(initState) + self.getAbstractions(initState)):
                    if s not in nextPath:
                        worklistPaths.append(nextPath + [s])
        return paths

    def invalidateStates(self, stateIds):
        invalidNodes = []
        for s in stateIds:
            invalidNodes.extend(self.transitiveClosureFromState(s))
        invalidNodes = sorted(list(set(invalidNodes)))

        newCfg = KCFG()
        nodeMap = {}
        for sid in self.init:
            if sid not in invalidNodes:
                (_, newSid) = newCfg.insertNode(self.states[sid])
                nodeMap[newSid] = sid
                newCfg.init.append(newSid)

        workList = list(newCfg.states.keys())
        while len(workList) > 0:
            newInitId = workList.pop(0)
            oldInitId = nodeMap[newInitId]

            for oldSuccessorId in [nid for nid in self.getSuccessors(oldInitId) if nid not in invalidNodes]:
                (_, newSuccessorId) = newCfg.insertNode(self.states[oldSuccessorId])
                if newSuccessorId in nodeMap:
                    continue
                nodeMap[newSuccessorId] = oldSuccessorId
                oldEdge = self.graph[oldInitId][oldSuccessorId]
                newCfg.insertEdge(newInitId, oldEdge['condition'], newSuccessorId, oldEdge['depth'], classes=oldEdge['classes'], priority=oldEdge['priority'])
                workList.append(newSuccessorId)

            for oldMoreGeneralId in [nid for nid in self.getMoreGeneralNodes(oldInitId) if nid not in invalidNodes]:
                (_, newMoreGeneralId) = newCfg.insertNode(self.states[oldMoreGeneralId])
                if newMoreGeneralId in nodeMap:
                    continue
                nodeMap[newMoreGeneralId] = oldMoreGeneralId
                workList.append(newMoreGeneralId)

        reverseNodeMap = {v: k for (k, v) in nodeMap.items()}
        for newNodeId in newCfg.states:
            if nodeMap[newNodeId] in self.abstractions:
                for oldAbstractId in self.abstractions[nodeMap[newNodeId]]:
                    if oldAbstractId in reverseNodeMap and reverseNodeMap[oldAbstractId] not in newCfg.abstractions[newNodeId]:
                        newCfg.abstractions[newNodeId].append(reverseNodeMap[oldAbstractId])

        for newNodeId in newCfg.states:
            if nodeMap[newNodeId] in self.loop:
                newCfg.loop.append(newNodeId)
            if nodeMap[newNodeId] in self.terminal:
                newCfg.terminal.append(newNodeId)
            if nodeMap[newNodeId] in self.stuck:
                newCfg.stuck.append(newNodeId)

        for target in self.target:
            (newState, newTargetId) = newCfg.insertNode(self.states[target])
            if newTargetId not in newCfg.target:
                newCfg.target.append(newTargetId)
            if newState:
                nodeMap[newTargetId] = target

        newCfg.frontier = [nid for nid in newCfg.states if nodeMap[nid] in self.frontier and nodeMap[nid] not in invalidNodes]
        for nodeId in newCfg.states:
            if len(newCfg.getSuccessors(nodeId)) < len(self.getSuccessors(nodeMap[nodeId])):
                newCfg.frontier.append(nodeId)
            if len(newCfg.getAbstractions(nodeId)) < len(self.getAbstractions(nodeMap[nodeId])):
                newCfg.frontier.append(nodeId)

        newCfg.frontier = list(sorted(list(set(newCfg.frontier))))

        notif('Invalidated nodes ' + str(shorten_hashes(invalidNodes)) + '.')
        notif('New frontier ' + str(shorten_hashes(newCfg.frontier)) + '.')
        self._assign(newCfg)
        return self

    def getPathsBetween(self, initNodeId, finalNodeId, seenNodes=None):
        if initNodeId == finalNodeId:
            return [[finalNodeId]]
        seen = [] if seenNodes is None else [nid for nid in seenNodes]
        succs = self.getSuccessors(initNodeId)
        abstr = self.getAbstractions(initNodeId)
        paths = []
        if initNodeId in seen:
            return []
        for nid in (succs + abstr):
            paths.extend([[initNodeId] + p for p in self.getPathsBetween(nid, finalNodeId, seenNodes=seen + [initNodeId])])
        return paths

    def getPathCondition(self, path):
        constraints = []
        substitutions = []
        depth = 0
        for (init, fin) in zip(path, path[1:]):
            if init in self.graph and fin in self.graph[init]:
                constraints.append(self.getEdgeCondition(init, fin))
                depth += self.graph[init][fin]['depth']
            if init in self.abstractions and fin in self.abstractions[init]:
                substitutions.append(self.subsumptions[init][fin])
        substitutions = list(reversed(substitutions))
        substitution = {}
        if len(substitutions) > 0:
            substitution = {k: substitutions[0][k] for k in substitutions[0]}
            for subst in substitutions[1:]:
                for k in substitution:
                    substitution[k] = substitute(substitution[k], subst)
        return (mlAnd(constraints), substitution, depth)
