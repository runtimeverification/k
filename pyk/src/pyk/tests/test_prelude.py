from typing import Final
from unittest import TestCase

from ..prelude import build_assoc, token
from .utils import f, x, y, z


class BuildAssocTest(TestCase):
    _0: Final = token('0')

    TEST_DATA: Final = (
        ((_0,), _0),
        ((x,), x),
        ((x, _0), x),
        ((_0, x), x),
        ((x, y), f(x, y)),
        ((_0, x, y), f(x, y)),
        ((x, _0, y), f(x, y)),
        ((x, y, _0), f(x, y)),
        ((x, y, z), f(x, f(y, z))),
        ((_0, x, y, z), f(x, f(y, z))),
        ((x, _0, y, z), f(x, f(y, z))),
        ((x, y, _0, z), f(x, f(y, z))),
        ((x, y, z, _0), f(x, f(y, z))),
        ((_0, x, _0, y, _0, z, _0), f(x, f(y, z))),
    )

    def test(self):
        for i, (terms, expected) in enumerate(self.TEST_DATA):
            with self.subTest(i=i):
                # When
                actual = build_assoc(self._0, f, terms)

                # Then
                self.assertEqual(actual, expected)
