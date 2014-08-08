// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Production;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Context;
import org.kframework.utils.StringUtil;

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
        Set<Ttuple> mytuples = new HashSet<Ttuple>();
        String varid = "[A-Z][a-zA-Z0-9\\']*";

        for (Terminal t1 : terminals) {
            for (Terminal t2 : terminals) {
                if (!t1.equals(t2)) {
                    if (t1.getTerminal().startsWith(t2.getTerminal())) {
                        Ttuple tt = new Ttuple();
                        tt.key = t1.getTerminal();
                        tt.value = t2.getTerminal();
                        String ending = tt.key.substring(tt.value.length());
                        if (ending.matches(varid))
                            mytuples.add(tt);
                    }
                }
            }
        }

        String sdf = "lexical restrictions\n";
        sdf += "    %% follow restrictions\n";
        for (Ttuple tt : mytuples) {
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
    private static class Ttuple {
        public String key;
        public String value;

        public boolean equals(Object o) {
            if (o.getClass() == Ttuple.class)
                return false;
            Ttuple tt = (Ttuple) o;
            if (key.equals(tt.key) && value.equals(tt.value))
                return true;
            return false;
        }

        public int hashCode() {
            return key.hashCode() + value.hashCode();
        }
    }
}
