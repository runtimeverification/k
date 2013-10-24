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
    priorityMap.put(0, new HashSet<Rule>());
    priorities.clear();
    for (Rule r : rules) {
      if (r.containsAttribute("priority")) {
        System.out.println(r.getAttribute("priority")); 
      }
      priorityMap.get(0).add(r);
    }
    iterator = priorityMap.get(0).iterator();
  }

  public Rule next() {
    return iterator.next();
  }

  public boolean hasNext() {
    return iterator.hasNext();
  }

  private Iterator<Rule> iterator;
  private HashMap<Integer, HashSet<Rule>> priorityMap;
  private TreeSet<Integer> priorities;
} 
