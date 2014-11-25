// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.util.ImpureFunctionException;

public class DummyBuiltinIOOperations implements BuiltinIOOperations {
    @Override
    public Term open(StringToken term1, StringToken term2, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term tell(IntToken term, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term getc(IntToken term, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term read(IntToken term1, IntToken term2, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term close(IntToken term, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term seek(IntToken term1, IntToken term2, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term putc(IntToken term1, IntToken term2, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term write(IntToken term1, StringToken term2, TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term parse(StringToken term1, StringToken term2,
            TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term parseInModule(StringToken term1, StringToken term2, StringToken term3,
                      TermContext termContext) {
        throw new ImpureFunctionException();
    }

    @Override
    public Term system(StringToken term, TermContext termContext) {
        throw new ImpureFunctionException();
    }
}
