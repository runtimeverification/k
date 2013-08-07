package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;

public class BuiltinIOOperations {

    public static FileSystem fs() {
        return BuiltinFunction.context().fileSystem();
    }

    public static Term open(StringToken term1, StringToken term2) {
        try {
            return IntToken.of(fs().open(term1.stringValue(), term2.stringValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term tell(IntToken term) {
        try {
            return IntToken.of(fs().get(term.longValue()).tell());
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term getc(IntToken term) {
        try {
            return IntToken.of(fs().get(term.longValue()).getc() & 0xff);
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term read(IntToken term1, IntToken term2) {
        try {
            return StringToken.of(new String(fs().get(term1.longValue()).read(term2.intValue())));
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    private static KItem processIOException(String errno) {
        String klabel = "'#" + errno;
        Definition def = BuiltinFunction.context().definition();
        assert def.kLabels().contains(klabel) : "No KLabel in definition for errno '" + errno + "'";
        return new KItem(KLabelConstant.of(klabel, def.context()), new KList(), def.context());
    }
}
