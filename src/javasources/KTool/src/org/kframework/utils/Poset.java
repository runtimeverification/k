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

import org.apache.commons.collections4.set.UnmodifiableSet;

import com.google.common.collect.ArrayTable;
import com.google.common.collect.Table;

public class Poset<T> implements Serializable {

    private boolean cacheEnabled = false;

    private java.util.Set<Tuple> relations = new HashSet<>();
    private java.util.Set<T> elements = new HashSet<>();

    public static <T> Poset<T> create() {
        return new Poset<T>();
    }

    /**
     * Returns a unmodifiable view of elements in this poset.
     */
    public java.util.Set<T> getElements() {
        return java.util.Collections.unmodifiableSet(elements);
    }

    public void addElement(T element) {
        elements.add(element);
        invalidateCache();
    }

    public void addRelation(T big, T small) {
        relations.add(new Tuple(big, small));
        elements.add(big);
        elements.add(small);
        invalidateCache();
    }

    public boolean isInRelation(T big, T small) {
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

    public T getMaxim(T start) {
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
        public abstract boolean isInRelation(T first, T second);

        public Table<T, T, Set<T>> cache;
    }

    private BoundType lowerBound = new BoundType() {

        @Override
        public boolean isInRelation(T first, T second) {
            return Poset.this.isInRelation(first, second);
        }
    };

    private BoundType upperBound = new BoundType() {

        @Override
        public boolean isInRelation(T first, T second) {
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
    public T getLUB(Set<T> subset) {
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
    public T getGLB(Set<T> subset) {
        return getUniqueBound(subset, lowerBound);
    }

    private T getUniqueBound(Set<T> subset, BoundType type) {
        if (subset == null || subset.size() == 0) {
            return null;
        }
        if (subset.size() == 1) {
            return subset.iterator().next();
        }
        Set<T> lowerBounds = getBounds(subset, type);
        if (lowerBounds.size() == 0) {
            return null;
        }

        T candidate = null;
        for (T lowerBound : lowerBounds) {
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
            for (T lowerBound : lowerBounds) {
                if (lowerBound != candidate && !type.isInRelation(candidate, lowerBound)) {
                    candidate = null;
                    break;
                }
            }
        }
        return candidate;
    }

    private Set<T> getBounds(Set<T> subset, BoundType type) {
        Set<T> bounds = new HashSet<>();
        for (T elem : elements) {
            boolean isBound = true;
            for (T subsetElem : subset) {
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

    private Set<T> getClosestBounds(Set<T> subset, BoundType type) {
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
            Iterator<T> iter = subset.iterator();
            T arg0 = iter.next();
            T arg1 = iter.next();
            Set<T> cachedBound = type.cache.get(arg0, arg1);
            if (cachedBound != null) {
                return cachedBound;
            }
        }

        Set<T> bounds = getBounds(subset, type);

        /* find closest bounds from the candidate bounds */
        if (!bounds.isEmpty()) {
            Set<T> nonClosestBs = new HashSet<T>();
            for (T bound1 : bounds) {
                // if bound1 has been identified as non-closest, elements closer than
                // that must have been also identified as non-closest in the same
                // outer loop
                if (!nonClosestBs.contains(bound1)) {
                    for (T bound2 : bounds) {
                        if (type.isInRelation(bound1, bound2)) {
                            nonClosestBs.add(bound2);
                        }
                    }
                }
            }

            bounds.removeAll(nonClosestBs);
        }

        /* make it immutable */
        bounds = UnmodifiableSet.unmodifiableSet(bounds);

        /* cache the result for the most common use case */
        if (subset.size() == 2) {
            Iterator<T> iter = subset.iterator();
            T arg0 = iter.next();
            T arg1 = iter.next();
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
    public Set<T> getMaximalLowerBounds(Set<T> subset) {
        return getClosestBounds(subset, lowerBound);
    }

    /**
     * Finds the minimal upper bounds of a subset of the elements in this poset.
     *
     * @param subset
     *            the subset of elements
     * @return an immutable set of the minimal upper bounds
     */
    public Set<T> getMinimalUpperBounds(Set<T> subset) {
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
        private T big, small;

        public Tuple(T big, T small) {
            this.big = big;
            this.small = small;
        }

        @Override
        public boolean equals(Object o) {
            if (o == null)
                return false;
            if (o.getClass() == Tuple.class) {
                @SuppressWarnings("unchecked")
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
    public List<T> checkForCycles() {
        // make next node list
        Set<T> nodes = new HashSet<>();
        Set<T> visited = new HashSet<>();

        for (Tuple t : relations) {
            nodes.add(t.big);
            nodes.add(t.small);
        }

        // DFS to search for a cycle
        for (T node : nodes) {
            if (!visited.contains(node)) {
                Stack<T> nodesStack = new Stack<>();
                Stack<Iterator<T>> iteratorStack = new Stack<>();
                nodesStack.push(node);
                visited.add(node);
                iteratorStack.push(nodes.iterator());

                while (nodesStack.size() > 0) {
                    Iterator<T> currentIterator = iteratorStack.peek();
                    T currentNode = nodesStack.peek();
                    while (currentIterator.hasNext()) {
                        T nextNode = currentIterator.next();
                        if (relations.contains(new Tuple(nextNode, currentNode))) {
                            if (nodesStack.contains(nextNode)) {
                                List<T> circuit = new ArrayList<>();
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

}
