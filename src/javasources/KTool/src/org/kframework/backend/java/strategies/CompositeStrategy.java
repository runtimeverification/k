package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Iterator;

public class CompositeStrategy implements Strategy {
    public CompositeStrategy() {
        children = new LinkedList<Strategy>();
    }

    public void push(Strategy s) {
        children.addFirst(s);
    }

    public Strategy pop() {
        return children.pollFirst();
    }

    public void reset(Collection<Rule> rules) {
        Iterator<Strategy> it = children.descendingIterator();
        while (it.hasNext()) {
            Strategy child = it.next();
            child.reset(rules);
            if (it.hasNext() && child.hasNext()) {
                rules = child.next();
            } else {
                break;
            }
        }
    }

    public Collection<Rule> next() {
        if (children.isEmpty()) {
            return null;
        }
        if (!children.peekFirst().hasNext()) {
            Strategy child = children.pollFirst();
            child.reset(next());
            children.addFirst(child);
        }
        return children.peekFirst().next();
    }

    public boolean hasNext() {
        if (children.isEmpty()) {
            return false;
        }
        boolean result = children.peekFirst().hasNext();
        if (!result) {
            Strategy child = children.pollFirst();
            result = hasNext();
            children.addFirst(child);
        }
        return result;
    }

    private LinkedList<Strategy> children;
}
