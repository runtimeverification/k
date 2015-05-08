// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.symbolic.KILtoBackendJavaKILTransformer;
import org.kframework.kil.Sort;
import org.kframework.krun.RunProcess;
import org.kframework.krun.RunProcess.ProcessOutput;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.io.IOException;
import java.nio.charset.CharacterCodingException;
import java.util.HashMap;
import java.util.Map;


/**
 * Table of {@code public static} methods for builtin IO operations.
 */
public class BuiltinIOOperations {

    private final FileSystem fs;
    private final Provider<KILtoBackendJavaKILTransformer> kilTransformer;
    private final Provider<RunProcess> rp;

    @Inject
    public BuiltinIOOperations(
            FileSystem fs,
            Provider<KILtoBackendJavaKILTransformer> kilTransformer,
            Provider<RunProcess> rp) {
        this.fs = fs;
        this.kilTransformer = kilTransformer;
        this.rp = rp;
    }

    public Term open(StringToken term1, StringToken term2, TermContext termContext) {
        try {
            return IntToken.of(fs.open(term1.stringValue(), term2.stringValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public Term tell(IntToken term, TermContext termContext) {
        try {
            return IntToken.of(fs.get(term.longValue()).tell());
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public Term getc(IntToken term, TermContext termContext) {
        try {
            return IntToken.of(fs.get(term.longValue()).getc() & 0xff);
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public Term read(IntToken term1, IntToken term2, TermContext termContext) {
        try {
            return StringToken.of(fs.get(term1.longValue()).read(term2.intValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

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

    public Term parse(StringToken term1, StringToken term2, TermContext termContext) {
        try {
            org.kframework.kil.Term kast = rp.get().runParser(
                    termContext.global().krunOptions.configurationCreation.parser(termContext.definition().context()),
                    term1.stringValue(), true, Sort.of(term2.stringValue()));
            Term term = kilTransformer.get().transformAndEval(kast);
            return term;
        } catch (ParseFailedException e) {
            return processIOException("noparse", termContext);
        }
    }

    public Term parseInModule(StringToken input, StringToken startSymbol, StringToken moduleName, TermContext termContext) {
        throw new RuntimeException("Not implemented!");
    }

    public Term system(StringToken term, TermContext termContext) {
        Map<String, String> environment = new HashMap<>();
        String[] args = term.stringValue().split("\001", -1);
        //for (String c : args) { System.out.println(c); }
        ProcessOutput output = RunProcess.execute(environment, termContext.global().files.getProcessBuilder(), args);

        KLabelConstant klabel = KLabelConstant.of("'#systemResult(_,_,_)", termContext.definition());
        /*
        String klabelString = "'#systemResult(_,_,_)";
        KLabelConstant klabel = KLabelConstant.of(klabelString, context);
        assert def.kLabels().contains(klabel) : "No KLabel in definition for " + klabelString;
        */
        String stdout = output.stdout != null ? output.stdout : "";
        String stderr = output.stderr != null ? output.stderr : "";
        return KItem.of(klabel, KList.concatenate(IntToken.of(output.exitCode),
            StringToken.of(stdout.trim()), StringToken.of(stderr.trim())), termContext);
    }

    private KItem processIOException(String errno, Term klist, TermContext termContext) {
        String klabelString = "'#" + errno;
        KLabelConstant klabel = KLabelConstant.of(klabelString, termContext.definition());
        assert termContext.definition().kLabels().contains(klabel) : "No KLabel in definition for errno '" + errno + "'";
        return KItem.of(klabel, klist, termContext);
    }

    private KItem processIOException(String errno, TermContext termContext) {
        return processIOException(errno, KList.EMPTY, termContext);
    }
}
