// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.Iterator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;

/**
 * The PriorityStrategy partitions rules such that rule a and rule b will be
 * in the same equivalence class iff a and b both have attribute "priority(x)"
 * where x is some integer. If a rule is not tagged with any priority it will
 * be given a priority of 0. Equivalence classes are returned in descending
 * priority order, begginning with the highest priority class.
 *
 * @author ericmikida
 *
 */

public class PriorityStrategy implements Strategy {
    public PriorityStrategy() {
        priorityMap = new java.util.HashMap<Integer, HashSet<Rule>>();
        priorities = new java.util.TreeSet<Integer>();
        priorityIterator = priorities.descendingIterator();
    }

    /**
     * Clears the priority list and rule map, then iterates through rules and
     * inserts each rule into the appropriate priority class in the map.
     */
    public void reset(Collection<Rule> rules) {
        priorityMap.clear();
        priorities.clear();
        for (Rule r : rules) {
            Integer p = 0;
            if (r.containsAttribute("priority")) {
                p = Integer.parseInt(r.getAttribute("priority"));
            }
            if (!priorityMap.containsKey(p)) {
                priorityMap.put(p, new HashSet<Rule>());
            }
            priorityMap.get(p).add(r);
            priorities.add(p);
        }
        priorityIterator = priorities.descendingIterator();
    }

    /**
     * Takes the next priority in the priority list and returns the
     * corresponding rule collection.
     */
    public Collection<Rule> next() {
        return priorityMap.get(priorityIterator.next());
    }

    /**
     * There is another class of rules iff there is another priority in the
     * priority list.
     **/
    public boolean hasNext() {
        return priorityIterator.hasNext();
    }

    private Iterator<Integer> priorityIterator;
    private HashMap<Integer, HashSet<Rule>> priorityMap;
    private TreeSet<Integer> priorities;
}
