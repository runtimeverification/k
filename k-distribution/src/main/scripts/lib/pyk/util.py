#!/usr/bin/env python3

import sys

def notif(msg):
    print()
    print(msg)
    print("".join(["=" for c in msg]))
    sys.stdout.flush()

def warning(msg):
    notif("[WARNING] " + msg)

def fatal(msg):
    notif(msg)
    sys.exit(1)

def combineDicts(*dicts):
    if len(dicts) == 0:
        return {}
    if len(dicts) == 1:
        return dicts[0]
    dict1 = dicts[0]
    dict2 = dicts[1]
    restDicts = dicts[2:]
    if dict1 is None or dict2 is None:
        return None
    intersecting_keys = set(dict1.keys()).intersection(set(dict2.keys()))
    for key in intersecting_keys:
        if dict1[key] != dict2[key]:
            return None
    newDict = { key : dict1[key] for key in dict1 }
    for key in dict2.keys():
        newDict[key] = dict2[key]
    return combineDicts(newDict, *restDicts)

