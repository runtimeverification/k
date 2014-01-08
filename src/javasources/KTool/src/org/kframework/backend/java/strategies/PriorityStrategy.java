package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.Iterator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;

public class PriorityStrategy implements Strategy {
    public PriorityStrategy() {
        priorityMap = new java.util.HashMap<Integer, HashSet<Rule>>();
        priorities = new java.util.TreeSet<Integer>();
        priorityIterator = priorities.descendingIterator();
    }

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

    public Collection<Rule> next() {
        return priorityMap.get(priorityIterator.next());
    }

    public boolean hasNext() {
        return priorityIterator.hasNext();
    }

    private Iterator<Integer> priorityIterator;
    private HashMap<Integer, HashSet<Rule>> priorityMap;
    private TreeSet<Integer> priorities;
}
