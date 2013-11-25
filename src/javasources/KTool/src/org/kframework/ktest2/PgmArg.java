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
        else if (arg.startsWith("c"))
            // HACK ALERT: the reason we need this check is this:
            // config file parser assumes long names and it removes all '-' prefix, and it works
            // fine because we're using long names in config files, except for -c... parameters.
            // so we need to handle -c parameters here
            return "-" + arg + "=" + val;
        return "--" + arg + "=" + val;
    }
}
