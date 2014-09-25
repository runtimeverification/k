// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;

public interface BuiltinIOOperations {
    public Term open(StringToken term1, StringToken term2, TermContext termContext);
    public Term tell(IntToken term, TermContext termContext);
    public Term getc(IntToken term, TermContext termContext);
    public Term read(IntToken term1, IntToken term2, TermContext termContext);
    public Term close(IntToken term, TermContext termContext);
    public Term seek(IntToken term1, IntToken term2, TermContext termContext);
    public Term putc(IntToken term1, IntToken term2, TermContext termContext);
    public Term write(IntToken term1, StringToken term2, TermContext termContext);
    public Term parse(StringToken term1, StringToken term2, TermContext termContext);
    public Term system(StringToken term, TermContext termContext);
}
