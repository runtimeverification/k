package org.kframework.ktest2.Test;


import java.util.List;

public class KRunProgram {

    public final List<String> args;
    public final String inputFile;
    public final String outputFile;
    public final String errorFile;

    public KRunProgram(List<String> args, String inputFile, String outputFile, String errorFile) {
        this.args = args;
        this.inputFile = inputFile;
        this.outputFile = outputFile;
        this.errorFile = errorFile;
    }
}
