package org.kframework.ktest2;

/**
 * Represents a program argument. `val' may be null, in that case argument is passed without value.
 */
public class PgmArg {

    public final String arg;
    public final String val;

    public PgmArg(String arg, String val) {
        this.arg = arg;
        this.val = val;
    }

    @Override
    public String toString() {
        if (val == null || val.equals("")) {
            if (arg.startsWith("-"))
                return arg;
            else
                return "--" + arg;
        }
        if (arg.startsWith("-"))
            return arg + "=" + val;
        return "--" + arg + "=" + val;
    }
}
