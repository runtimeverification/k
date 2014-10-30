// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.ktest.Test;

import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest.ExecNames;
import org.kframework.ktest.PgmArg;
import org.kframework.utils.OS;
import org.kframework.utils.StringUtil;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class KRunProgram {

    public final TestCase testCase;
    public final String pgmName;
    public final String pgmPath;
    public final File defPath;
    public final List<PgmArg> args;
    public final File inputFile;
    public final File outputFile;
    public final File errorFile;
    public final File newOutputFile;
    public final boolean regex;

    public KRunProgram(TestCase testCase, String pgmPath, File defPath, List<PgmArg> args,
                       File inputFile, File outputFile, File errorFile, File newOutputFile,
                       boolean regex) {
        this.testCase = testCase;
        this.pgmName = FilenameUtils.getBaseName(pgmPath);
        this.pgmPath = pgmPath;
        this.defPath = defPath;
        this.args = args;
        this.inputFile = inputFile;
        this.outputFile = outputFile;
        this.errorFile = errorFile;
        this.newOutputFile = newOutputFile;
        this.regex = regex;
    }

    /**
     * @return command array to pass process builder
     */
    public String[] getKrunCmd() {
        List<String> stringArgs = new ArrayList<>();
        stringArgs.add(ExecNames.getKrun());
        stringArgs.add(pgmPath);
        for (PgmArg arg : args) {
            stringArgs.addAll(arg.toStringList());
        }
        String[] argsArr = stringArgs.toArray(new String[stringArgs.size()]);
        if (OS.current() == OS.WIN) {
            for (int i = 0; i < argsArr.length; i++) {
                argsArr[i] = StringUtil.escapeShell(argsArr[i], OS.current());
            }
        }
        return argsArr;
    }
}
