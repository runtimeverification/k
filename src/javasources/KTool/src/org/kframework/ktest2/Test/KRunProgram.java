package org.kframework.ktest2.Test;


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
}
