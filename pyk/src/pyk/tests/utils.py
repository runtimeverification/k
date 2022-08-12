from ..kast import KApply, KLabel, KVariable

a, b, c = map(KApply, ('a', 'b', 'c'))
x, y, z = map(KVariable, ('x', 'y', 'z'))
f, g, h = map(KLabel, ('f', 'g', 'h'))

k = KLabel('<k>')
