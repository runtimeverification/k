package org.kframework.ktest.Test;


import org.kframework.ktest.ExecNames;

import java.util.List;

public class KRunProgram {

    public final String pgmName;
    public final List<String> args;
    public final String inputFile;
    public final String outputFile;
    public final String errorFile;

    public KRunProgram(String pgmName, List<String> args, String inputFile, String outputFile,
                       String errorFile) {
        this.pgmName = pgmName;
        this.args = args;
        this.inputFile = inputFile;
        this.outputFile = outputFile;
        this.errorFile = errorFile;
    }

    /**
     * @return command array to pass process builder
     */
    public String[] getKrunCmd() {
        String[] args1 = new String[args.size() + 1];
        args1[0] = ExecNames.getKrun();
        for (int i = 1; i < args1.length; i++)
            args1[i] = args.get(i - 1);
        return args1;
    }
}
