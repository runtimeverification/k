// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableMap;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.util.KSorts;

import java.util.*;

/**
 * Class containing helper static methods for {@link org.kframework.backend.java.kil.BuiltinMap}.
 *
 * @author AndreiS
 */
public class BuiltinMapUtils {

    public static final BuiltinMapUtils EMPTY = new BuiltinMapUtils(
            Collections.<Term, Term>emptyMap(),
            Collections.<KItem>emptyList(),
            Collections.<Variable>emptyList(),
            Collections.<KItem>emptyList());

    public static BuiltinMapUtils merge(BuiltinMapUtils builtinMapUtils1, BuiltinMapUtils builtinMapUtils2) {
        Map<Term, Term> entries = new HashMap<>();
        List<KItem> patterns = new ArrayList<>();
        List<Variable> variables = new ArrayList<>();
        List<KItem> rest = new ArrayList<>();

        entries.putAll(builtinMapUtils1.entries);
        patterns.addAll(builtinMapUtils1.patterns);
        variables.addAll(builtinMapUtils1.variables);
        rest.addAll(builtinMapUtils1.rest);

        entries.putAll(builtinMapUtils2.entries);
        patterns.addAll(builtinMapUtils2.patterns);
        variables.addAll(builtinMapUtils2.variables);
        rest.addAll(builtinMapUtils2.rest);
        return new BuiltinMapUtils(entries, patterns, variables, rest);
    }

    public final Map<Term, Term> entries;
    public final List<KItem> patterns;
    public final List<Variable> variables;
    public final List<KItem> rest;

    public BuiltinMapUtils(Map<Term, Term> entries, List<KItem> patterns, List<Variable> variables, List<KItem> rest) {
        this.entries = entries;
        this.patterns = patterns;
        this.variables = variables;
        this.rest = rest;
    }

    public static Map<Term, Term> getMapEntries(Term term) {
        return getBuiltinMapUtils(term).entries;
    }

    public static List<KItem> getMapPatterns(Term term) {
        return getBuiltinMapUtils(term).patterns;
    }

    public static List<Variable> getMapVariables(Term term) {
        return getBuiltinMapUtils(term).variables;
    }

    public static boolean isNormalMap(Term term) {
        return term.sort().equals(KSorts.MAP)
                && getMapVariables(term).size() <= 1
                && getBuiltinMapUtils(term).rest.isEmpty();
    }

    public static BuiltinMapUtils getBuiltinMapUtils(Term term) {
        if (!term.sort().equals(KSorts.MAP)) {
            return EMPTY;
        }

        if (term instanceof KList) {
            assert ((KList) term).size() == 1 && !((KList) term).hasFrame();
            term = ((KList) term).get(0);
        }
        if (term instanceof KSequence) {
            assert ((KSequence) term).size() == 1 && !((KSequence) term).hasFrame();
            term = ((KSequence) term).get(0);
        }

        if (term instanceof KItem
                && ((KItem) term).kLabel() instanceof KLabel
                && ((KItem) term).kList() instanceof KList) {
            if (((KItem) term).kLabel().toString().equals("'_Map_")) {
                return merge(
                        getBuiltinMapUtils(((KList) ((KItem) term).kList()).get(0)),
                        getBuiltinMapUtils(((KList) ((KItem) term).kList()).get(1)));
            } else if (((KLabel) ((KItem) term).kLabel()).isPattern()) {
                return new BuiltinMapUtils(
                    Collections.<Term, Term>emptyMap(),
                    Collections.singletonList((KItem) term),
                    Collections.<Variable>emptyList(),
                    Collections.<KItem>emptyList());
            } else {
                return new BuiltinMapUtils(
                    Collections.<Term, Term>emptyMap(),
                    Collections.<KItem>emptyList(),
                    Collections.<Variable>emptyList(),
                    Collections.singletonList((KItem) term));
            }
        } else if (term instanceof BuiltinMap) {
            return new BuiltinMapUtils(
                ImmutableMap.copyOf(((BuiltinMap) term).getEntries()),
                Collections.<KItem>emptyList(),
                ((BuiltinMap) term).hasFrame() ?
                        Collections.singletonList(((BuiltinMap) term).frame()) :
                        Collections.<Variable>emptyList(),
                Collections.<KItem>emptyList());
        } else if (term instanceof Variable) {
            return new BuiltinMapUtils(
                Collections.<Term, Term>emptyMap(),
                Collections.<KItem>emptyList(),
                Collections.singletonList((Variable) term),
                Collections.<KItem>emptyList());
        }

        assert false;
        return null;
    }

}
