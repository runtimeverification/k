// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.*;

/**
 * A CompositeStrategy is used to combine multiple to strategies together in
 * a stack. Strategies can be pushed and popped onto the composite strategy.
 * When resetting a composite strategy the rules are passed to the bottom of
 * the stack. Once the bottom strategy has partitioned the rules, it's next()
 * class of rules is passed to the strategy above it to be partitioned. This
 * propogates to the top of the stack, until the top strategy receives a set
 * of rules to partition.
 *
 * For example: If we have a transition strategy on top of a priority strategy,
 * we will first get the highest priority rules from the priority strategy, then
 * partition them with the transition strategy. If instead, the priority
 * strategy is on top, then we will first get the structural rules from the
 * transition strategy, then partition them with the priority strategy.
 *
 * When getting the next equivalence class from a composite strategy, we first
 * attempt to get it from the top strategy. If it does not have a next class
 * we pop it from the stack, and retry with the next strategy. Once we get a
 * next class of rules we pass it in through the strategies again, as we add
 * them back to the stack until we eventually get back to the top of the stack.
 *
 * @author ericmikida
 *
 */

public class CompositeStrategy implements Strategy {
    public CompositeStrategy() {
        stack = new LinkedList<>();
    }

    public void push(Strategy s) {
        stack.addFirst(s);
    }

    public Strategy pop() {
        return stack.pollFirst();
    }

    /**
     * The CompositeStrategy is reset from the bottom up. We start at the bottom
     * and partition the rules with each successive strategy until we reach the
     * top. Once the reset is complete, the top strategy will be primed to
     * return an equivalence class of rules that is the composite application of
     * each strategy in the stack.
     */
    public void reset(Collection<Rule> rules) {
        Iterator<Strategy> it = stack.descendingIterator();
        // With each iteration we pare down the rules and move up the stack
        // until we reach the top.
        while (it.hasNext()) {
            Strategy top = it.next();
            top.reset(rules);
            // If the current strategy has a next set of rules to return, and
            // the iterator hasn't reached the top of the stack, then take the
            // next set of rules and go to the next iteration.
            if (it.hasNext() && top.hasNext()) {
                rules = top.next();
            } else {
                // If partitioning the rules does not yield any equivalence
                // classes then we should stop early. Applying the stack of
                // strategies to the original set of rules leaves us with no
                // legal rules to try.
                break;
            }
        }
    }

    /**
     * Search for the next set of rules starting at the the top of
     * the stack. Only search down the stack if the top has no more equivalence
     * classes to return.
     */
    public Collection<Rule> next() {
        while (!stack.isEmpty()) {
            Strategy s = stack.pop();
            if (s.hasNext()) {
                Collection<Rule> ret = s.next();
                stack.push(s);
                return ret;
            }
        }
        throw new NoSuchElementException("No equivalence classes left in the CompositeStrategy. " +
                "Have you checked hasNext()?");
    }

    /**
     * Search in strategy stack to see if there is a next class by checking each
     * strategy.hasNext(), starting at the top of the stack and ending early
     * once we encounter a true.
     */
    public boolean hasNext() {
        for (Strategy s : stack) {
            if (s.hasNext()) {
                return true;
            }
        }
        return false;
    }

    private LinkedList<Strategy> stack;
}
