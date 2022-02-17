import hashlib
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple, TypeVar

T = TypeVar('T')


def combineDicts(*dicts: Mapping) -> Optional[Dict]:
    if len(dicts) == 0:
        return {}
    if len(dicts) == 1:
        return dict(dicts[0])
    dict1 = dicts[0]
    dict2 = dicts[1]
    restDicts = dicts[2:]
    if dict1 is None or dict2 is None:
        return None
    intersecting_keys = set(dict1.keys()).intersection(set(dict2.keys()))
    for key in intersecting_keys:
        if dict1[key] != dict2[key]:
            return None
    newDict = {key: dict1[key] for key in dict1}
    for key in dict2.keys():
        newDict[key] = dict2[key]
    return combineDicts(newDict, *restDicts)


def findCommonItems(l1: Iterable[T], l2: Iterable[T]) -> Tuple[List[T], List[T], List[T]]:
    common = []
    for i in l1:
        if i in l2:
            common.append(i)
    newL1 = []
    newL2 = []
    for i in l1:
        if i not in common:
            newL1.append(i)
    for i in l2:
        if i not in common:
            newL2.append(i)
    return (common, newL1, newL2)


def dedupe(xs: Iterable[T]) -> List[T]:
    res = []
    for x in xs:
        if x not in res:
            res.append(x)
    return res


def getAppliedAxiomList(debugLogFile: Path) -> List[List[str]]:
    axioms = []
    next_axioms = []
    with open(debugLogFile, 'r') as logFile:
        for line in logFile:
            if line.find('DebugTransition') > 0:
                if line.find('after  apply axioms:') > 0:
                    next_axioms.append(line[line.find('after  apply axioms:') + len('after  apply axioms:'):])
                elif len(next_axioms) > 0:
                    axioms.append(next_axioms)
                    next_axioms = []
    return axioms


def strHash(k: Any) -> str:
    hash = hashlib.sha256()
    hash.update(str(k).encode('utf-8'))
    return str(hash.hexdigest())
