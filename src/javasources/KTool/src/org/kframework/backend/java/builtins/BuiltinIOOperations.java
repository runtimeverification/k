// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;

import java.io.IOException;
import java.nio.charset.CharacterCodingException;


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
            return KLabelInjection.injectionOf(KSequence.EMPTY, context);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), context),
                    context);
        }
    }

    public static Term seek(IntToken term1, IntToken term2, TermContext context) {
        try {
            fs(context).get(term1.longValue()).seek(term2.longValue());
            return KLabelInjection.injectionOf(KSequence.EMPTY, context);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), context),
                    context);
        }
    }

    public static Term putc(IntToken term1, IntToken term2, TermContext context) {
        try {
            fs(context).get(term1.longValue()).putc(term2.unsignedByteValue());
            return KLabelInjection.injectionOf(KSequence.EMPTY, context);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), context),
                    context);
        }
    }

    public static Term write(IntToken term1, StringToken term2, TermContext context) {
        try {
            fs(context).get(term1.longValue()).write(term2.byteArrayValue());
            return KLabelInjection.injectionOf(KSequence.EMPTY, context);
        } catch (CharacterCodingException e) {
            throw new IllegalArgumentException(e);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), context),
                    context);
        }
    }

    public static Term parse(StringToken term1, StringToken term2, TermContext context) {
        try {
            RunProcess rp = new RunProcess();
            org.kframework.kil.Term kast = rp.runParser(
                    context(context).ccOptions.parser(context(context)), 
                    term1.stringValue(), true, term2.stringValue(), context(context));
            Term term = Term.of(kast, definition(context));
            term = term.evaluate(context);
            return term;
        } catch (ParseFailedException e) {
            return processIOException("noparse", context);
        }
    }

    private static KItem processIOException(String errno, TermContext context) {
        String klabelString = "'#" + errno;
        Definition def = context.definition();
        KLabelConstant klabel = KLabelConstant.of(klabelString, context.definition());
        assert def.kLabels().contains(klabel) : "No KLabel in definition for errno '" + errno + "'";
        return KItem.of(klabel, KList.EMPTY, context);
    }
}
