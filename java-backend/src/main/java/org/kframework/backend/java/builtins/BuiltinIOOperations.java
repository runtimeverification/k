// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kore.KORE;
import org.kframework.krun.RunProcess;
import org.kframework.krun.RunProcess.ProcessOutput;
import org.kframework.krun.api.io.FileSystem;

import java.io.File;
import java.io.IOException;
import java.nio.charset.CharacterCodingException;
import java.util.HashMap;
import java.util.Map;
import org.kframework.utils.OS;


/**
 * Table of {@code public static} methods for builtin IO operations.
 */
public class BuiltinIOOperations {

    public static Term getTime(TermContext termContext) {
        return IntToken.of(System.currentTimeMillis());
    }

    public static Term open(StringToken term1, StringToken term2, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            return IntToken.of(fs.open(term1.stringValue(), term2.stringValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public static Term tell(IntToken term, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            return IntToken.of(fs.get(term.longValue()).tell());
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public static Term getc(IntToken term, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            return IntToken.of(fs.get(term.longValue()).getc() & 0xff);
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public static Term read(IntToken term1, IntToken term2, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            return StringToken.of(fs.get(term1.longValue()).read(term2.intValue()));
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public static Term close(IntToken term, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            fs.close(term.longValue());
            return BuiltinList.kSequenceBuilder(termContext.global()).build();
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public static Term seek(IntToken term1, IntToken term2, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            fs.get(term1.longValue()).seek(term2.longValue());
            return BuiltinList.kSequenceBuilder(termContext.global()).build();
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public static Term putc(IntToken term1, IntToken term2, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            fs.get(term1.longValue()).putc(term2.unsignedByteValue());
            return BuiltinList.kSequenceBuilder(termContext.global()).build();
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }
    public static Term write(IntToken term1, StringToken term2, TermContext termContext) {
        FileSystem fs = termContext.fileSystem();
        try {
            fs.get(term1.longValue()).write(term2.byteArrayValue());
            return BuiltinList.kSequenceBuilder(termContext.global()).build();
        } catch (CharacterCodingException e) {
            throw new IllegalArgumentException(e);
        } catch (IOException e) {
            return processIOException(e.getMessage(), termContext);
        }
    }

    public static Term system(StringToken term, TermContext termContext) {
        Map<String, String> environment = new HashMap<>();
        String[] args = term.stringValue().split("\001", -1);
        //for (String c : args) { System.out.println(c); }
        ProcessOutput output = RunProcess.execute(environment, termContext.global().files.getProcessBuilder(), args);

        KLabelConstant klabel = KLabelConstant.of(KORE.KLabel("#systemResult(_,_,_)"), termContext.definition());
        /*
        String klabelString = "#systemResult(_,_,_)";
        KLabelConstant klabel = KLabelConstant.of(klabelString, context);
        assert def.kLabels().contains(klabel) : "No KLabel in definition for " + klabelString;
        */
        String stdout = output.stdout != null ? new String(output.stdout) : "";
        String stderr = output.stderr != null ? new String(output.stderr) : "";
        return KItem.of(klabel, KList.concatenate(IntToken.of(output.exitCode),
                StringToken.of(stdout.trim()), StringToken.of(stderr.trim())), termContext.global());
    }

    /**
     * Executes the given command line with `sh -c 'cmd'` on unix
     * and `cmd /c 'cmd'` on windows.
     * @param term
     * @param termContext
     * @return a #systemResult term containing the exit code, stdout:String, stderr:String
     */
    public static Term spawn(StringToken term, TermContext termContext) {
        Map<String, String> environment = new HashMap<>();
        String[] args = new String[3];
        if (OS.current() == OS.WINDOWS) {
            args[0] = "cmd";
            args[1] = "/c";
        } else {
            args[0] = "sh";
            args[1] = "-c";
        }
        args[2] = term.stringValue();
        ProcessOutput output = RunProcess.execute(environment, termContext.global().files.getProcessBuilder(), args);

        KLabelConstant klabel = KLabelConstant.of(KORE.KLabel("#systemResult(_,_,_)_K-IO"), termContext.definition());
        String stdout = output.stdout != null ? new String(output.stdout) : "";
        String stderr = output.stderr != null ? new String(output.stderr) : "";
        return KItem.of(klabel, KList.concatenate(IntToken.of(output.exitCode),
                StringToken.of(stdout.trim()), StringToken.of(stderr.trim())), termContext.global());
    }

    public static Term tempFilename(StringToken prefix, StringToken suffix, TermContext termContext) throws IOException {
        return StringToken.of(File.createTempFile("tmp" + prefix.stringValue(), suffix.stringValue()).getAbsolutePath());
    }

    public static Term remove(StringToken fname, TermContext termContext) {
        File f = new File(fname.stringValue());
        if (f.delete())
            return BuiltinList.kSequenceBuilder(termContext.global()).build();
        else
            return processIOException("EPERM", termContext);
    }

    private static KItem processIOException(String errno, Term klist, TermContext termContext) {
        String klabelString = "#" + errno;
        KLabelConstant klabel = KLabelConstant.of(KORE.KLabel(klabelString), termContext.definition());
        assert termContext.definition().kLabels().contains(klabel) : "No KLabel in definition for errno '" + errno + "'";
        return KItem.of(klabel, klist, termContext.global());
    }

    private static KItem processIOException(String errno, TermContext termContext) {
        return processIOException(errno, KList.EMPTY, termContext);
    }
}
