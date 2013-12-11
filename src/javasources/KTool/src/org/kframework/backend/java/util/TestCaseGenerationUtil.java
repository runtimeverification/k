package org.kframework.backend.java.util;

import java.util.ArrayList;
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
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

public class TestCaseGenerationUtil {

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

    public static Term getSimplestTermOfSort(String sort, Context context) {
        // TODO(YilongL): This is cheating; fix it!
        switch (sort) {
        case "Block":
            return new KItem(KLabelConstant.of("'{}", context), new KList(), context);
            
        case "BExp":
            return BoolToken.TRUE;

        default:
            break;
        }
        return null;
    }        
}
