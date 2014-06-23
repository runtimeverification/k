// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import org.apache.commons.collections15.set.UnmodifiableSet;
import com.google.common.collect.ArrayTable;
import com.google.common.collect.Table;

public class Poset implements Serializable {

    private boolean cacheEnabled = false;
    
    private java.util.Set<Tuple> relations = new HashSet<Tuple>();
    private java.util.Set<String> elements = new HashSet<String>();
        
    /**
     * Returns a unmodifiable view of elements in this poset.
     */
    public java.util.Set<String> getElements() {
        return java.util.Collections.unmodifiableSet(elements);
    }
    
    public void addElement(String element) {
        elements.add(element);
        invalidateCache();
    }

    public void addRelation(String big, String small) {
        relations.add(new Tuple(big, small));
        elements.add(big);
        elements.add(small);
        invalidateCache();
    }

    public boolean isInRelation(String big, String small) {
        return relations.contains(new Tuple(big, small));
    }

    public void transitiveClosure() {
        boolean finished = false;
        while (!finished) {
            finished = true;
            Set<Tuple> ssTemp = new HashSet<Tuple>();
            for (Tuple s1 : relations) {
                for (Tuple s2 : relations) {
                    if (s1.big.equals(s2.small)) {
                        Tuple sTemp = new Tuple(s2.big, s1.small);
                        if (!relations.contains(sTemp)) {
                            ssTemp.add(sTemp);
                            finished = false;
                        }
                    }
                }
            }
            relations.addAll(ssTemp);
        }
    }

    public String getMaxim(String start) {
        boolean maxim = true;
        do {
            maxim = true;
            for (Tuple sbs : relations) {
                if (sbs.small.equals(start)) {
                    start = sbs.big;
                    maxim = false;
                }
            }
        } while (!maxim);
        return start;
    }

    private abstract class BoundType implements Serializable {
        public abstract boolean isInRelation(String first, String second);
        
        public Table<String, String, Set<String>> cache;
    }
    
    private BoundType lowerBound = new BoundType() {
        
        @Override
        public boolean isInRelation(String first, String second) {
            return Poset.this.isInRelation(first, second);
        }
    };
    
    private BoundType upperBound = new BoundType() {
        
        @Override
        public boolean isInRelation(String first, String second) {
            return Poset.this.isInRelation(second, first);
        }
    };

    /**
     * finds the least upper bound of a subset of the elements of
     * 
     * returns null if none exists
     * 
     * assumes that all elements in subset are actually elements of the Poset
     * 
     * also assumes that the Poset is actually a Poset (transitively closed)
     * 
     */
    public String getLUB(Set<String> subset) {
        return getUniqueBound(subset, upperBound);
    }

    /**
     * finds the greatest lower bound of a subset of the elements of
     * 
     * returns null if none exists
     * 
     * assumes that all elements in subset are actually elements of the Poset
     * 
     * also assumes that the Poset is actually a Poset (transitively closed)
     * 
     */
    public String getGLB(Set<String> subset) {
        return getUniqueBound(subset, lowerBound);
    }
    
    private String getUniqueBound(Set<String> subset, BoundType type) {
        if (subset == null || subset.size() == 0) {
            return null;
        }
        if (subset.size() == 1) {
            return subset.iterator().next();
        }
        Set<String> lowerBounds = getBounds(subset, type);
        if (lowerBounds.size() == 0) {
            return null;
        }
        
        String candidate = null;
        for (String lowerBound : lowerBounds) {
            if (candidate == null) {
                candidate = lowerBound;
            } else {
                if (type.isInRelation(lowerBound, candidate)) {
                    candidate = lowerBound;
                } else if (!type.isInRelation(candidate, lowerBound)) {
                    /* no relation between lowerBound and candidate; none of them is the GLB */
                    candidate = null;
                }
            }
        }
        /* if there is a GLB, it must be candidate */
        if (candidate != null) {
            for (String lowerBound : lowerBounds) {
                if (lowerBound != candidate && !type.isInRelation(candidate, lowerBound)) {
                    candidate = null;
                    break;
                }
            }
        }
        return candidate;
    }

    private Set<String> getBounds(Set<String> subset, BoundType type) {
        Set<String> bounds = new HashSet<String>();
        for (String elem : elements) {
            boolean isBound = true;
            for (String subsetElem : subset) {
                if (!(type.isInRelation(subsetElem, elem) || elem.equals(subsetElem))) {
                    isBound = false;
                    break;
                }
            }
            if (isBound) {
                bounds.add(elem);
            }
        }
        return bounds;
    }
    
    private Set<String> getClosestBounds(Set<String> subset, BoundType type) {
        assert elements.containsAll(subset);
        
        if (subset == null || subset.size() == 0) {
            return Collections.emptySet();
        }
        if (subset.size() == 1) {
            return Collections.singleton(subset.iterator().next());
        }
        
        if (subset.size() == 2) {
            if (!cacheEnabled) {
                initializeCache();
            }
            Iterator<String> iter = subset.iterator();
            String arg0 = iter.next();
            String arg1 = iter.next();
            Set<String> cachedBound = type.cache.get(arg0, arg1);
            if (cachedBound != null) {
                return cachedBound;
            }
        }
        
        Set<String> bounds = getBounds(subset, type);
        
        /* find closest bounds from the candidate bounds */
        if (!bounds.isEmpty()) {
            Set<String> nonClosestBs = new HashSet<String>();
            for (String bound1 : bounds) {
                // if bound1 has been identified as non-closest, elements closer than
                // that must have been also identified as non-closest in the same
                // outer loop
                if (!nonClosestBs.contains(bound1)) {
                    for (String bound2 : bounds) {
                        if (type.isInRelation(bound1, bound2)) {
                            nonClosestBs.add(bound2);
                        }
                    }
                }
            }
        
            bounds.removeAll(nonClosestBs);
        }

        /* make it immutable */
        bounds = UnmodifiableSet.decorate(bounds);

        /* cache the result for the most common use case */
        if (subset.size() == 2) {
            Iterator<String> iter = subset.iterator();
            String arg0 = iter.next();
            String arg1 = iter.next();
            type.cache.put(arg0, arg1, bounds);
            type.cache.put(arg1, arg0, bounds);
        }
        return bounds;
    }
    
    /**
     * Finds the maximal lower bounds of a subset of the elements in this poset.
     * 
     * @param subset
     *            the subset of elements
     * @return an immutable set of the maximal lower bounds
     */
    public Set<String> getMaximalLowerBounds(Set<String> subset) {
        return getClosestBounds(subset, lowerBound);
    }
    
    /**
     * Finds the minimal upper bounds of a subset of the elements in this poset.
     * 
     * @param subset
     *            the subset of elements
     * @return an immutable set of the minimal upper bounds
     */
    public Set<String> getMinimalUpperBounds(Set<String> subset) {
        return getClosestBounds(subset, upperBound);
    }
    
    private void invalidateCache() {
        cacheEnabled = false;
        lowerBound.cache = null;
        upperBound.cache = null;
    }
    
    private void initializeCache() {
        cacheEnabled = true;
        lowerBound.cache = ArrayTable.create(elements, elements);
        upperBound.cache = ArrayTable.create(elements, elements);
    }    

    private class Tuple implements Serializable {
        private String big, small;

        public Tuple(String big, String small) {
            this.big = big;
            this.small = small;
        }

        @Override
        public boolean equals(Object o) {
            if (o == null)
                return false;
            if (o.getClass() == Tuple.class) {
                Tuple s1 = (Tuple) o;
                return s1.big.equals(big) && s1.small.equals(small);
            }
            return false;
        }

        @Override
        public int hashCode() {
            return big.hashCode() + small.hashCode();
        }

        @Override
        public String toString() {
            return small + " < " + big;
        }
    }

    /**
     * Checks to see if the current set of relations has a circuit.
     * 
     * @return null if there aren't any circuits, or a list of relations that create a circuit.
     */
    public List<String> checkForCycles() {
        // make next node list
        Set<String> nodes = new HashSet<String>();
        Set<String> visited = new HashSet<String>();

        for (Tuple t : relations) {
            nodes.add(t.big);
            nodes.add(t.small);
        }

        // DFS to search for a cycle
        for (String node : nodes) {
            if (!visited.contains(node)) {
                Stack<String> nodesStack = new Stack<String>();
                Stack<Iterator<String>> iteratorStack = new Stack<Iterator<String>>();
                nodesStack.push(node);
                visited.add(node);
                iteratorStack.push(nodes.iterator());

                while (nodesStack.size() > 0) {
                    Iterator<String> currentIterator = iteratorStack.peek();
                    String currentNode = nodesStack.peek();
                    while (currentIterator.hasNext()) {
                        String nextNode = currentIterator.next();
                        if (relations.contains(new Tuple(nextNode, currentNode))) {
                            if (nodesStack.contains(nextNode)) {
                                List<String> circuit = new ArrayList<String>();
                                for (int i = nodesStack.indexOf(nextNode); i < nodesStack.size(); i++) {
                                    circuit.add(nodesStack.elementAt(i));
                                }
                                return circuit;
                            }
                            if (!visited.contains(nextNode)) {
                                nodesStack.push(nextNode);
                                iteratorStack.push(nodes.iterator());
                                visited.add(nextNode);
                                break;
                            }
                        }
                    }
                    // does not have next... pop
                    if (!currentIterator.hasNext()) {
                        nodesStack.pop();
                        iteratorStack.pop();
                    }
                }
            }
        }
        return null;
    }

    // a small test to verify if LUB works
    // should print Exps
    public static void main(String[] args) {
        System.out.println("msg");
        Poset p = new Poset();
        p.addRelation("K", "Exps");
        p.addRelation("Exps", "Vals");
        p.addRelation("Exps", "Ids");
        p.transitiveClosure();
        Set<String> input = new HashSet<String>();
        input.add("K");
        input.add("Exps");
        input.add("Vals");
        input.add("Ids");
        System.out.println(p.getLUB(input));
    }
}
