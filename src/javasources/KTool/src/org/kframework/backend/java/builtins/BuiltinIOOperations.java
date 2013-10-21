package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.K;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.nio.charset.CharacterCodingException;

public class BuiltinIOOperations {

    public static FileSystem fs() {
        return BuiltinFunction.context().fileSystem();
    }

    public static Definition definition() {
        return BuiltinFunction.context().definition();
    }

    public static Context context() {
        return BuiltinFunction.context().definition().context();
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
        } catch (RuntimeException e) {
            throw e;
        }
    }

    public static Term read(IntToken term1, IntToken term2) {
        try {
            return StringToken.of(fs().get(term1.longValue()).read(term2.intValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term close(IntToken term) {
        try {
            fs().close(term.longValue());
            return new KSequence();
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term seek(IntToken term1, IntToken term2) {
        try {
            fs().get(term1.longValue()).seek(term2.longValue());
            return new KSequence();
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term putc(IntToken term1, IntToken term2) {
        try {
            fs().get(term1.longValue()).putc(term2.unsignedByteValue());
            return new KSequence();
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term write(IntToken term1, StringToken term2) {
        try {
            fs().get(term1.longValue()).write(term2.byteArrayValue());
            return new KSequence();
        } catch (CharacterCodingException e) {
            throw new IllegalArgumentException(e);
        } catch (IOException e) {
            return processIOException(e.getMessage());
        }
    }

    public static Term parse(StringToken term1, StringToken term2) {
        try {
            RunProcess rp = new RunProcess();
            org.kframework.kil.Term kast = rp.runParser(K.parser, term1.stringValue(), true, term2.stringValue(), context());
            Term term = Term.of(kast, definition());
            term = term.evaluate(BuiltinFunction.context());
            return term;
        } catch (TransformerException e) {
            return processIOException("noparse");
        }
    }

    private static KItem processIOException(String errno) {
        String klabelString = "'#" + errno;
        Definition def = BuiltinFunction.context().definition();
        KLabelConstant klabel = KLabelConstant.of(klabelString, def.context());
        assert def.kLabels().contains(klabel) : "No KLabel in definition for errno '" + errno + "'";
        return new KItem(klabel, new KList(), def.context());
    }
}
