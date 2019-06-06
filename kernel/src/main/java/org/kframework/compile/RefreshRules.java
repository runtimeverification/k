// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.definition.Rule;
import org.kframework.kore.K;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * refreshes variable names in terms and sentences according to alpha equivalence.
 * Variables that have previously been refreshed are not normalized on succeeding passes,
 * allowing the user to fine-tune the applyRefresh process such that arbitrary subterms can share
 * a common prefix.
 */
public class RefreshRules {

    private final Set<String> avoidVars;
    private int counter = 0;
    private Map<KVariable, String> vars = new HashMap<>();

    public RefreshRules(Set<String> avoidVars) {
        this.avoidVars = avoidVars;
    }

    /**
     * Refreshes a rule
     * @param rule The rule to be refreshed.
     * @return The refreshed version of {@code rule}, in which each variable
     * is alpha-renamed to fresh variable.
     * name.
     */
    public static Rule refresh(Rule rule) {
        return new RefreshRules(new HashSet<>()).applyRefresh(rule);
    }

    /**
     * Refreshes a set of rules such that no two rules would have variables in common.
     * @param rules The rules to be refreshed.
     * @return The refreshed version of {@code rules}
     */
    public static Collection<Rule> refresh(Collection<Rule> rules, Set<String> avoidVars) {
        RefreshRules refreshRules = new RefreshRules(avoidVars);
        return rules.stream().map(refreshRules::applyRefreshResetVars).collect(Collectors.toCollection(LinkedList::new));
    }

    private Rule applyRefresh(Rule rule) {
        return Rule(
                applyRefresh(rule.body()),
                applyRefresh(rule.requires()),
                applyRefresh(rule.ensures()),
                rule.att());
    }

    private Rule applyRefreshResetVars(Rule rule) {
        vars.clear();
        return applyRefresh(rule);
    }

    private K applyRefresh(K term) {
        return new TransformK() {
            @Override
            public K apply(KVariable var) {
                if (var.att().contains("refreshed"))
                    return var;
                if (!vars.containsKey(var)) {
                    String newVarName;
                    do {
                        newVarName = "_" + counter++;
                    } while (avoidVars.contains(newVarName));
                    vars.put(var, newVarName);
                }
                return KVariable(vars.get(var), var.att().add("refreshed", var.name()));
            }
        }.apply(term);
    }


}
