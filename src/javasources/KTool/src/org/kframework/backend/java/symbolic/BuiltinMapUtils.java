package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by andrei on 6/4/14.
 */
public class BuiltinMapUtils {

    public static Map<Term, Term> getMapEntries(Term term) {
        Map<Term, Term> entries = new HashMap<>();
        if (term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabel
                && ((KItem) term).kList() instanceof KList) {
            if (((KItem) term).kLabel().toString().equals("'_Map_")) {
                entries.putAll(getMapEntries(((KList) ((KItem) term).kList()).get(0)));
                entries.putAll(getMapEntries(((KList) ((KItem) term).kList()).get(1)));
            }
        } else if (term instanceof BuiltinMap) {
            entries.putAll(((BuiltinMap) term).getEntries());
        }
        return entries;
    }

    public static List<KItem> getMapPatterns(Term term) {
        List<KItem> patterns = new ArrayList<>();
        if (term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabel
                && ((KItem) term).kList() instanceof KList) {
            if (((KItem) term).kLabel().toString().equals("'_Map_")) {
                patterns.addAll(getMapPatterns(((KList) ((KItem) term).kList()).get(0)));
                patterns.addAll(getMapPatterns(((KList) ((KItem) term).kList()).get(1)));
            } else if (((KLabel) ((KItem) term).kLabel()).isPattern()) {
                patterns.add((KItem) term);
            }
        }
        return patterns;
    }
}
