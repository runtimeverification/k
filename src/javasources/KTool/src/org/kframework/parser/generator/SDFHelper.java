// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.generator;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Attributes;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.utils.StringUtil;

public class SDFHelper {
    public static String getSDFAttributes(Attributes attrs) {
        String str = " {";
        if (attrs.getContents().size() == 0)
            return "";

        // if (attrs.containsKey("prefer"))
        // str += "prefer, ";
        // if (attrs.containsKey("avoid"))
        // str += "avoid, ";
        if (attrs.containsKey("left"))
            str += "left, ";
        if (attrs.containsKey("reject"))
            str += "reject, ";
        if (attrs.containsKey("right"))
            str += "right, ";
        if (attrs.containsKey("non-assoc"))
            str += "non-assoc, ";
        // if (attrs.containsKey("bracket")) // should not need this since we use the Bracket class
        // str += "bracket, ";
        if (attrs.containsKey("cons"))
            str += "cons(\"" + attrs.get("cons") + "\"), ";

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
        if (context.productions.containsKey(tag))
            return context.productions.get(tag);
        else
            return new HashSet<Production>();
    }

    public static String getFollowRestrictionsForTerminals(Set<String> terminals) {
        Set<Ttuple> mytuples = new HashSet<Ttuple>();
        String varid = "[A-Z][a-zA-Z0-9\\']*";

        for (String t1 : terminals) {
            for (String t2 : terminals) {
                if (!t1.equals(t2)) {
                    if (t1.startsWith(t2)) {
                        Ttuple tt = new Ttuple();
                        tt.key = t1;
                        tt.value = t2;
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
            sdf += "    \"" + StringUtil.escape(tt.value) + "\" -/- ";
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
