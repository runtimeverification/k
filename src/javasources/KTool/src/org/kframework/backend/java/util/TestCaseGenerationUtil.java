package org.kframework.backend.java.util;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import org.kframework.backend.java.kil.ConstrainedTerm;

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
}
