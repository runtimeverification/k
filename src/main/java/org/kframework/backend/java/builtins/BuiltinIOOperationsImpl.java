// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.KilFactory;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.RunProcess;
import org.kframework.krun.api.io.FileSystem;

import com.google.inject.Inject;

import java.io.IOException;
import java.nio.charset.CharacterCodingException;
import java.util.Map;
import java.util.HashMap;


/**
 * Table of {@code public static} methods for builtin IO operations.
 */
public class BuiltinIOOperationsImpl implements BuiltinIOOperations {

    private final Definition def;
    private final FileSystem fs;
    private final Context context;
    private final ConfigurationCreationOptions ccOptions;
    private final KilFactory kilFactory;

    @Inject
    public BuiltinIOOperationsImpl(
            Definition def,
            FileSystem fs,
            Context context,
            ConfigurationCreationOptions ccOptions,
            KilFactory kilFactory) {
        this.def = def;
        this.fs = fs;
        this.context = context;
        this.ccOptions = ccOptions;
        this.kilFactory = kilFactory;
    }

    @Override
    public Term open(StringToken term1, StringToken term2, TermContext termContext) {
        try {
            return IntToken.of(fs.open(term1.stringValue(), term2.stringValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    @Override
    public Term tell(IntToken term, TermContext termContext) {
        try {
            return IntToken.of(fs.get(term.longValue()).tell());
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    @Override
    public Term getc(IntToken term, TermContext termContext) {
        try {
            return IntToken.of(fs.get(term.longValue()).getc() & 0xff);
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    @Override
    public Term read(IntToken term1, IntToken term2, TermContext termContext) {
        try {
            return StringToken.of(fs.get(term1.longValue()).read(term2.intValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    @Override
    public Term close(IntToken term, TermContext termContext) {
        try {
            fs.close(term.longValue());
            return KLabelInjection.injectionOf(KSequence.EMPTY, termContext);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), termContext),
                    termContext);
        }
    }

    @Override
    public Term seek(IntToken term1, IntToken term2, TermContext termContext) {
        try {
            fs.get(term1.longValue()).seek(term2.longValue());
            return KLabelInjection.injectionOf(KSequence.EMPTY, termContext);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), termContext),
                    termContext);
        }
    }

    @Override
    public Term putc(IntToken term1, IntToken term2, TermContext termContext) {
        try {
            fs.get(term1.longValue()).putc(term2.unsignedByteValue());
            return KLabelInjection.injectionOf(KSequence.EMPTY, termContext);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), termContext),
                    termContext);
        }
    }

    @Override
    public Term write(IntToken term1, StringToken term2, TermContext termContext) {
        try {
            fs.get(term1.longValue()).write(term2.byteArrayValue());
            return KLabelInjection.injectionOf(KSequence.EMPTY, termContext);
        } catch (CharacterCodingException e) {
            throw new IllegalArgumentException(e);
        } catch (IOException e) {
            return KLabelInjection.injectionOf(
                    processIOException(e.getMessage(), termContext),
                    termContext);
        }
    }

    @Override
    public Term parse(StringToken term1, StringToken term2, TermContext termContext) {
        try {
            RunProcess rp = new RunProcess();
            org.kframework.kil.Term kast = rp.runParser(
                    ccOptions.parser(context),
                    term1.stringValue(), true, Sort.of(term2.stringValue()), context);
            Term term = kilFactory.term(kast);
            term = term.evaluate(termContext);
            return term;
        } catch (ParseFailedException e) {
            return processIOException("noparse", termContext);
        }
    }

    @Override
    public Term system(StringToken term, TermContext termContext) {
        RunProcess rp = new RunProcess();
        Map<String, String> environment = new HashMap<>();
        String[] args = term.stringValue().split("\001", -1);
        //for (String c : args) { System.out.println(c); }
        rp.execute(environment, args);

        KLabelConstant klabel = KLabelConstant.of("'#systemResult(_,_,_)", context);
        /*
        String klabelString = "'#systemResult(_,_,_)";
        KLabelConstant klabel = KLabelConstant.of(klabelString, context);
        assert def.kLabels().contains(klabel) : "No KLabel in definition for " + klabelString;
        */
        String stdout = rp.getStdout() != null ? rp.getStdout() : "";
        String stderr = rp.getErr()    != null ? rp.getErr()    : "";
        return KItem.of(klabel, KList.concatenate(IntToken.of(rp.getExitCode()),
            StringToken.of(stdout.trim()), StringToken.of(stderr.trim())), termContext);
    }

    private KItem processIOException(String errno, Term klist, TermContext termContext) {
        String klabelString = "'#" + errno;
        KLabelConstant klabel = KLabelConstant.of(klabelString, context);
        assert def.kLabels().contains(klabel) : "No KLabel in definition for errno '" + errno + "'";
        return KItem.of(klabel, klist, termContext);
    }

    private KItem processIOException(String errno, TermContext termContext) {
        return processIOException(errno, KList.EMPTY, termContext);
    }
}
