package org.kframework.ktest.Test;


import org.apache.commons.io.FilenameUtils;
import org.apache.commons.lang3.StringUtils;
import org.kframework.ktest.ExecNames;
import org.kframework.ktest.PgmArg;
import org.kframework.ktest.QuoteHandling;

import java.util.ArrayList;
import java.util.List;

public class KRunProgram {

    public final String pgmName;
    public final String pgmPath;
    public final String defPath;
    public final List<PgmArg> args;
    public final String inputFile;
    public final String outputFile;
    public final String errorFile;
    public final String newOutputFile;

    public KRunProgram(String pgmPath, String defPath, List<PgmArg> args, String inputFile, String outputFile,
                       String errorFile, String newOutputFile) {
        this.pgmName = FilenameUtils.getBaseName(pgmPath);
        this.pgmPath = pgmPath;
        this.defPath = defPath;
        this.args = args;
        this.inputFile = inputFile;
        this.outputFile = outputFile;
        this.errorFile = errorFile;
        this.newOutputFile = newOutputFile;
    }

    /**
     * @return command array to pass process builder
     */
    public String[] getKrunCmd() {
        List<String> stringArgs = new ArrayList<String>();
        stringArgs.add(ExecNames.getKrun());
        stringArgs.add(pgmPath);
        for (int i = 0; i < args.size(); i++) {
            stringArgs.addAll(args.get(i).toStringList());
        }
        String[] argsArr = new String[stringArgs.size()];
        return stringArgs.toArray(argsArr);
    }

    /**
     * @return String to be used in logging.
     */
    public String toLogString() {
    	return StringUtils.join(getKrunCmd(), " ");
    }
}
