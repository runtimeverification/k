import hashlib
from typing import Any, Dict, Iterable, List, Mapping, Optional, Tuple, TypeVar

T = TypeVar('T')


def combine_dicts(*dicts: Mapping) -> Optional[Dict]:
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
    return combine_dicts(newDict, *restDicts)


def find_common_items(l1: Iterable[T], l2: Iterable[T]) -> Tuple[List[T], List[T], List[T]]:
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


def hash_str(x: Any) -> str:
    hash = hashlib.sha256()
    hash.update(str(x).encode('utf-8'))
    return str(hash.hexdigest())
