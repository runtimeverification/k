from ..kast import KApply, KLabel, KVariable

a, b, c = map(KApply,    ('a', 'b', 'c'))  # noqa: E241
x, y, z = map(KVariable, ('x', 'y', 'z'))  # noqa: E241
f, g, h = map(KLabel,    ('f', 'g', 'h'))  # noqa: E241

k = KLabel('<k>')
