// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Production;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Context;
import org.kframework.utils.StringUtil;

import com.google.common.base.Preconditions;
import com.google.common.collect.BiMap;

public class SDFHelper {
    public static String getSDFAttributes(Production p, BiMap<String, Production> conses) {
        String str = " {";

        // if (attrs.containsKey("prefer"))
        // str += "prefer, ";
        // if (attrs.containsKey("avoid"))
        // str += "avoid, ";
        if (p.containsAttribute("left"))
            str += "left, ";
        if (p.containsAttribute("reject"))
            str += "reject, ";
        if (p.containsAttribute("right"))
            str += "right, ";
        if (p.containsAttribute("non-assoc"))
            str += "non-assoc, ";
        // if (attrs.containsKey("bracket")) // should not need this since we use the Bracket class
        // str += "bracket, ";
        if (conses.containsValue(p))
            str += "cons(\"" + conses.inverse().get(p) + "\"), ";

        if (str.endsWith(", "))
            return str.substring(0, str.length() - 2) + "}";
        else
            return str + "}";
    }

    /**
     * Search for all the productions that have either 'klabel(tag)' or the 'tag' attribute
     *
     * @param tag
     * @return
     */
    public static Set<Production> getProductionsForTag(String tag, Context context) {
        return context.tags.get(tag);
    }

    public static String getFollowRestrictionsForTerminals(Set<Terminal> terminals) {
        Set<Tuple> mytuples = new HashSet<Tuple>();
        String varid = "[A-Z][a-zA-Z0-9\\']*";

        for (Terminal t1 : terminals) {
            for (Terminal t2 : terminals) {
                if (!t1.equals(t2)) {
                    if (t1.getTerminal().startsWith(t2.getTerminal())) {
                        Tuple tt = new Tuple(t1.getTerminal(), t2.getTerminal());
                        String ending = tt.key.substring(tt.value.length());
                        if (ending.matches(varid))
                            mytuples.add(tt);
                    }
                }
            }
        }

        String sdf = "lexical restrictions\n";
        sdf += "    %% follow restrictions\n";
        for (Tuple tt : mytuples) {
            sdf += "    " + StringUtil.enquoteCString(tt.value) + " -/- ";
            String ending = tt.key.substring(tt.value.length());
            for (int i = 0; i < ending.length(); i++) {
                String ch = "" + ending.charAt(i);
                if (ch.matches("[a-zA-Z]"))
                    sdf += "[" + ch + "].";
                else
                    sdf += "[\\" + ch + "].";
            }
            sdf = sdf.substring(0, sdf.length() - 1) + "\n";
        }

        return sdf;
    }

    /**
     * Using this class to collect the prefixes amongst terminals
     *
     * @author RaduFmse
     *
     */
    private final static class Tuple {
        private String key;
        private String value;

        public Tuple(String key, String value) {
            Preconditions.checkNotNull(key);
            Preconditions.checkNotNull(value);
            this.key = key;
            this.value = value;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + key.hashCode();
            result = prime * result + value.hashCode();
            return result;
        }
        @Override
        public boolean equals(Object obj) {
            if (this == obj)
                return true;
            if (obj == null)
                return false;
            if (getClass() != obj.getClass())
                return false;
            Tuple other = (Tuple) obj;
            if (!key.equals(other.key))
                return false;
            if (!value.equals(other.value))
                return false;
            return true;
        }
    }
}
