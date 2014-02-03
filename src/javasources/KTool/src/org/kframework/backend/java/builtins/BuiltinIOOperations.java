package org.kframework.backend.java.builtins;

import java.io.IOException;
import java.nio.charset.CharacterCodingException;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.K;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;

/**
 * Table of {@code public static} methods for builtin IO operations.
 */
public class BuiltinIOOperations {

    public static FileSystem fs(TermContext context) {
        return context.fileSystem();
    }

    public static Definition definition(TermContext context) {
        return context.definition();
    }

    public static Context context(TermContext context) {
        return context.definition().context();
    }

    public static Term open(StringToken term1, StringToken term2, TermContext context) {
        try {
            return IntToken.of(fs(context).open(term1.stringValue(), term2.stringValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        }
    }

    public static Term tell(IntToken term, TermContext context) {
        try {
            return IntToken.of(fs(context).get(term.longValue()).tell());
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        }
    }

    public static Term getc(IntToken term, TermContext context) {
        try {
            return IntToken.of(fs(context).get(term.longValue()).getc() & 0xff);
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        } catch (RuntimeException e) {
            throw e;
        }
    }

    public static Term read(IntToken term1, IntToken term2, TermContext context) {
        try {
            return StringToken.of(fs(context).get(term1.longValue()).read(term2.intValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        }
    }

    public static Term close(IntToken term, TermContext context) {
        try {
            fs(context).close(term.longValue());
            return new KItem(new KLabelInjection(new KSequence()), new KList(), context.definition().context());
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        }
    }

    public static Term seek(IntToken term1, IntToken term2, TermContext context) {
        try {
            fs(context).get(term1.longValue()).seek(term2.longValue());
            return new KItem(new KLabelInjection(new KSequence()), new KList(), context.definition().context());
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        }
    }

    public static Term putc(IntToken term1, IntToken term2, TermContext context) {
        try {
            fs(context).get(term1.longValue()).putc(term2.unsignedByteValue());
            return new KItem(new KLabelInjection(new KSequence()), new KList(), context.definition().context());
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        }
    }

    public static Term write(IntToken term1, StringToken term2, TermContext context) {
        try {
            fs(context).get(term1.longValue()).write(term2.byteArrayValue());
            return new KItem(new KLabelInjection(new KSequence()), new KList(), context.definition().context());
        } catch (CharacterCodingException e) {
            throw new IllegalArgumentException(e);
        } catch (IOException e) {
            return processIOException(e.getMessage(), context);
        }
    }

    public static Term parse(StringToken term1, StringToken term2, TermContext context) {
        try {
            RunProcess rp = new RunProcess();
            org.kframework.kil.Term kast = rp.runParser(K.parser, term1.stringValue(), true, term2.stringValue(), context(context));
            Term term = Term.of(kast, definition(context));
            term = term.evaluate(context);
            return term;
        } catch (TransformerException e) {
            return processIOException("noparse", context);
        }
    }

    private static KItem processIOException(String errno, TermContext context) {
        String klabelString = "'#" + errno;
        Definition def = context.definition();
        KLabelConstant klabel = KLabelConstant.of(klabelString, def.context());
        assert def.kLabels().contains(klabel) : "No KLabel in definition for errno '" + errno + "'";
        return new KItem(klabel, new KList(), def.context());
    }
}
