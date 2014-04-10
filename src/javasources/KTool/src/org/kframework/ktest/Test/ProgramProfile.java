package org.kframework.ktest.Test;

import java.util.List;

import org.kframework.ktest.PgmArg;

/**
 * A set of information used to specify the behavior for executing some subset of KRun programs.
 * For example, a profile might represent all programs, or it might represent programs individually.
 *
 */
public class ProgramProfile {
    private List<PgmArg> args;
    private boolean regex;
    
    public ProgramProfile(List<PgmArg> args, boolean regex) {
        this.args = args;
        this.regex = regex;
    }
    
    public List<PgmArg> getArgs() {
        return args;
    }
    
    public boolean isRegex() {
        return regex;
    }
}
