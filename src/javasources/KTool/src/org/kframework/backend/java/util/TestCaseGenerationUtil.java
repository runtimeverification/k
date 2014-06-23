// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

public class TestCaseGenerationUtil {

    public static final String TESTGEN_CATEGORY_UNTAGGED = "UNTAGGED";
    public static final String ATTRIBUTE_TESTGEN_CATEGORY = "testgen-category";

    /**
     * Selects a certain number of states randomly from the given list of
     * states.
     * 
     * @param listOfStates
     *            a list of states
     * @param n
     *            the number of states to be selected
     * @return a list of the selected states
     */
    public static List<ConstrainedTerm> getArbitraryStates(
            List<ConstrainedTerm> listOfStates, int n) {
        assert n >= 0;
        
        List<ConstrainedTerm> results = new ArrayList<ConstrainedTerm>();
        ArrayList<Integer> numbersAvail = new ArrayList<Integer>();

        for (int i = 0; i < listOfStates.size(); i++)
            numbersAvail.add(i);
        
        // fixed initial seed
        Random rnd = new Random(0);
        while ((n > 0) && (numbersAvail.size() > 0)) {
            int kth = rnd.nextInt(numbersAvail.size());
            results.add(listOfStates.get(numbersAvail.get(kth)));
            numbersAvail.remove(kth);
            n--;
        }
        return results;
    }

    /**
     * Selects a certain number of states randomly from the given list following
     * a round-robin fashion with respect to different categories.
     * 
     * @param listOfStates
     *            a list of states
     * @param listOfRules
     *            a list of rules associated with the list of states
     * @param n
     *            the number of states to be selected
     * @return a list of selected states
     */
    public static List<ConstrainedTerm> getStatesByRR(
            List<ConstrainedTerm> listOfStates, List<Rule> listOfRules, int n) {
        assert (listOfStates.size() == listOfRules.size()) && (n >= 0);
        if (listOfStates.isEmpty()) {
            return Collections.emptyList();
        }
        
        n = Math.min(n, listOfStates.size());
        
        List<ConstrainedTerm> results = new ArrayList<ConstrainedTerm>();
        boolean[] isRemoved = new boolean[listOfStates.size()];
        Map<String, Integer> cat2NumOfStates = new HashMap<String, Integer>();
        Map<String, Integer> quotas = new HashMap<String, Integer>();
        List<Integer> indirectIdx = new ArrayList<Integer>();

        for (int i = 0; i < listOfStates.size(); i++) {
            isRemoved[i] = false;
            
            String category = getValOfAttrTestGenCategory(listOfRules.get(i));
            if (cat2NumOfStates.get(category) == null) {
                cat2NumOfStates.put(category, 0);
            }
            cat2NumOfStates.put(category, cat2NumOfStates.get(category) + 1);
            
            indirectIdx.add(i);
        }
        Collections.shuffle(indirectIdx);
        
        int avg = n / cat2NumOfStates.keySet().size();
        int left = n;
        for (String category : cat2NumOfStates.keySet()) {
            int quota = Math.min(avg, cat2NumOfStates.get(category));
            quotas.put(category, quota);
            left -= quota;
        }
        while (left > 0) {
            for (String category : cat2NumOfStates.keySet()) {
                if (quotas.get(category) < cat2NumOfStates.get(category) && left > 0) {
                    quotas.put(category, quotas.get(category) + 1);
                    left--;
                }
            }
        }
        
        for (int i = 0; i < listOfStates.size(); i++) {
            Integer idx = indirectIdx.get(i);
            String category = getValOfAttrTestGenCategory(listOfRules.get(idx));
            if ((!isRemoved[idx]) && (quotas.get(category) > 0)) {
                results.add(listOfStates.get(idx));
                quotas.put(category, quotas.get(category) - 1);
                isRemoved[idx] = true;
                n--;
            }
        }
        
        for (String category: quotas.keySet()) {
            assert quotas.get(category) == 0;
        }
        assert n == 0;
            
        return results;
    }            

    public static List<ConstrainedTerm> getMostConcreteStates(
            List<ConstrainedTerm> listOfStates, int n, Context context) {
        List<ConstrainedTerm> results = new ArrayList<ConstrainedTerm>();
        
        Map<ConstrainedTerm, Integer> numOfFreeVars = new HashMap<ConstrainedTerm, Integer>();
        for (ConstrainedTerm state : listOfStates) {
            numOfFreeVars.put(state, getNumOfFreeVars(state, context));
        }
        
        for (int i = 0; i < n; i++) {
            ConstrainedTerm nextState = null;
            for (ConstrainedTerm state : listOfStates) {
                if (numOfFreeVars.get(state) == null) continue;
                if ((nextState == null)
                        || (numOfFreeVars.get(state) < numOfFreeVars.get(nextState))) {
                    nextState = state;
                }
            }
            
            if (nextState == null) break;
            results.add(nextState);
            numOfFreeVars.remove(nextState);
        }
        
        return results;
    }

    public static int getNumOfFreeVars(ConstrainedTerm cnstrTerm, Context context) {
        Set<Variable> set = cnstrTerm.term().variableSet();
        for (Iterator<Variable> iter = set.iterator(); iter.hasNext();) {
            if (context.isSubsortedEq("KResult", iter.next().sort())) {
                iter.remove();
            }
        }
        return set.size();
    }

    public static Term getSimplestTermOfSort(String sort, TermContext termContext) {
        // TODO(YilongL): This is cheating; fix it!
        switch (sort) {
        case "Block":
            return KItem.of(KLabelConstant.of("'{}", termContext.definition()), KList.EMPTY, termContext);
            
        case "BExp":
            return BoolToken.TRUE;

        default:
            break;
        }
        return null;
    }

    public static void updateRuleDistStats(Map<String, Integer> stats,
            List<Rule> rules) {
        for (Rule rule : rules) {
            String category = getValOfAttrTestGenCategory(rule);
            Integer cnt = stats.get(category);
            if (cnt == null) {
                stats.put(category, 0);
            }
            stats.put(category, stats.get(category) + 1);
        }               
    }
    
    private static String getValOfAttrTestGenCategory(Rule rule) {
        String category = rule.getAttribute(ATTRIBUTE_TESTGEN_CATEGORY);
        if (category == null) {
            category = TESTGEN_CATEGORY_UNTAGGED;
        }
        return category;
    }
}
