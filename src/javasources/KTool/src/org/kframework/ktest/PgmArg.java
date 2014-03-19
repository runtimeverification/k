package org.kframework.ktest;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import org.apache.commons.lang3.StringUtils;

/**
 * Represents a program argument. `val' may be null, in that case argument is passed without value.
 */
public class PgmArg {

    public final String arg;
    public final String key;
    public final String val;

    public PgmArg(String arg, String val) {
        this(arg, null, val);
    }

    public PgmArg(String arg, String key, String val) {
        this.arg = arg;
        this.key = key;
        this.val = val;
    }
    
    public List<String> toStringList() {
        String arg = this.arg;
        String val = this.val;
        //if (key != null) {
        //    return Collections.singletonList(arg + key + "=" + val);
        if (val == null || val.equals("")) {
            return Collections.singletonList(arg);
        } else {
            return Arrays.asList(arg, val);
        }
    }
    
    @Override
    public String toString() {
        return StringUtils.join(toStringList(), " ");
    }
}
