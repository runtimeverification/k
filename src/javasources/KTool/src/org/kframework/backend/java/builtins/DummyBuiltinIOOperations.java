// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

public class DummyBuiltinIOOperations implements BuiltinIOOperations {
    @Override
    public Term open(StringToken term1, StringToken term2, TermContext termContext) {
        return null;
    }

    @Override
    public Term tell(IntToken term, TermContext termContext) {
        return null;
    }

    @Override
    public Term getc(IntToken term, TermContext termContext) {
        return null;
    }

    @Override
    public Term read(IntToken term1, IntToken term2, TermContext termContext) {
        return null;
    }

    @Override
    public Term close(IntToken term, TermContext termContext) {
        return null;
    }

    @Override
    public Term seek(IntToken term1, IntToken term2, TermContext termContext) {
        return null;
    }

    @Override
    public Term putc(IntToken term1, IntToken term2, TermContext termContext) {
        return null;
    }

    @Override
    public Term write(IntToken term1, StringToken term2, TermContext termContext) {
        return null;
    }

    @Override
    public Term parse(StringToken term1, StringToken term2,
            TermContext termContext) {
        return null;
    }
}
