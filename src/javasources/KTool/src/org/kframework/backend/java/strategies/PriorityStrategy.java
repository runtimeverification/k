package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.Iterator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.TreeSet;

public class PriorityStrategy extends Strategy {
  public PriorityStrategy() {
    priorityMap = new java.util.HashMap<Integer,HashSet<Rule>>();
    priorities = new java.util.TreeSet<Integer>();
  }

  public void apply(Collection<Rule> rules) {
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

  public Rule next() {
    if (ruleIterator == null || !ruleIterator.hasNext()) {
      ruleIterator = priorityMap.get(priorityIterator.next()).iterator();
    }
    return ruleIterator.next();
  }

  public boolean hasNext() {
    return priorityIterator.hasNext() || ruleIterator.hasNext();
  }

  private Iterator<Integer> priorityIterator;
  private Iterator<Rule> ruleIterator;
  private HashMap<Integer, HashSet<Rule>> priorityMap;
  private TreeSet<Integer> priorities;
} 
