// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class VarHashMap extends HashMap<String, Set<String>> {

    private static final long serialVersionUID = 1L;

    public int hashCode() {
        int code = 0;
        for (Map.Entry<String, Set<String>> entry : this.entrySet()) {
            code += entry.getKey().hashCode();
            for (String s : entry.getValue())
                code += s.hashCode();
        }
        return code;
    }

    public boolean equals(Object obj) {
        if (obj == null)
            return false;
        if (obj == this)
            return true;
        if (obj instanceof VarHashMap) {
            VarHashMap vhm = (VarHashMap) obj;
            if (this.size() != vhm.size())
                return false;
            for (Map.Entry<String, Set<String>> entry : this.entrySet()) {
                if (!vhm.containsKey(entry.getKey()))
                    return false;
                Set<String> target = vhm.get(entry.getKey());
                if (entry.getValue().size() != target.size())
                    return false;
                for (String s : entry.getValue())
                    if (!target.contains(s))
                        return false;
            }
        } else
            return false;
        return true;
    }
}
