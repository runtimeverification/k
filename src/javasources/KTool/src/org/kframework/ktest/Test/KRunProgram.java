package org.kframework.ktest.Test;


import org.apache.commons.io.FilenameUtils;
import org.kframework.ktest.ExecNames;
import org.kframework.ktest.PgmArg;

import java.util.List;

public class KRunProgram {

    public final String pgmName;
    public final String pgmPath;
    public final List<PgmArg> args;
    public final String inputFile;
    public final String outputFile;
    public final String errorFile;

    public KRunProgram(String pgmPath, List<PgmArg> args, String inputFile, String outputFile,
                       String errorFile) {
        this.pgmName = FilenameUtils.getBaseName(pgmPath);
        this.pgmPath = pgmPath;
        this.args = args;
        this.inputFile = inputFile;
        this.outputFile = outputFile;
        this.errorFile = errorFile;
    }

    /**
     * @return command array to pass process builder
     */
    public String[] getKrunCmd() {
        String[] args1 = new String[args.size() + 2];
        args1[0] = ExecNames.getKrun();
        args1[1] = pgmPath;
        for (int i = 2; i < args1.length; i++)
            args1[i] = args.get(i - 2).toString();
        return args1;
    }
}
