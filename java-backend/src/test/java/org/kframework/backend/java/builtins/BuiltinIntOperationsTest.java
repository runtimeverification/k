// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.junit.Test;
import org.kframework.backend.java.kil.TermContext;
import org.mockito.Mock;

import static org.junit.Assert.*;

public class BuiltinIntOperationsTest {

    @Mock
    TermContext context;

    @Test
    public void testediv() {
        testediv(-1, -1, 1, 0);
        testediv(7, 3, 2, 1);
        testediv(7, -3, -2, 1);
        testediv(-7, 3, -3, 2);
        testediv(-7, -3, 3, 2);
        testediv(123, 12, 10, 3);
        testediv(123, -12, -10, 3);
        testediv(-123, 12, -11, 9);
        testediv(-123, -12, 11, 9);
        testediv(123, 1233, 0, 123);
        testediv(123, -1233, 0, 123);
        testediv(-123, 1233, -1, 1110);
        testediv(-123, -1233, 1, 1110);
    }

    // a = b*q + r, 0 <= r < |b| - Euclidean division where the remainder is always positive
    private void testediv(long a, long b, long q, long r) {
        assert(0 <= r && r < Math.abs(b));
        assert(a == b * q + r);
        assertEquals(IntToken.of(q), BuiltinIntOperations.ediv(IntToken.of(a), IntToken.of(b), context));
        assertEquals(IntToken.of(r), BuiltinIntOperations.rem(IntToken.of(a), IntToken.of(b), context));
    }
}
