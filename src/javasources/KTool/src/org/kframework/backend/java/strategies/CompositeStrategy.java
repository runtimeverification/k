// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.strategies;

import org.kframework.backend.java.kil.Rule;

import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Iterator;

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
        stack = new LinkedList<Strategy>();
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
     * Recursively search for the next set of rules starting at the the top of
     * the stack. Only recurse down the stack if the top has no more equivalence
     * classes to return.
     */
    public Collection<Rule> next() {
        if (stack.isEmpty()) {
            return null;
        }
        // If the top of the stack doesn't have a next class to return, then
        // pop it off the stack and try again. Once we find a next class we
        // will pull it back up the recursion, applying it to each successive
        // strategy on the way back up.
        if (!stack.peekFirst().hasNext()) {
            // Pop the first element so the subsequent recursive call to next()
            // will be operating on the next strategy in the stack.
            Strategy top = stack.pollFirst();
            // Apply the result of the recursive call to the top strategy.
            top.reset(next());
            stack.addFirst(top);
        }
        // TODO(YilongL): I have no idea why children.peekFirst().next() could
        // return duplicate elements.
        return new LinkedHashSet<Rule>(stack.peekFirst().next());
    }

    /**
     * Recursively check to see if there is a next class by checking each
     * strategy.hasNext(), starting at the top of the stack and ending early
     * once we encounter a true.
     */
    public boolean hasNext() {
        if (stack.isEmpty()) {
            return false;
        }
        boolean result = stack.peekFirst().hasNext();
        // If the top item doesn't have a next class, pop it off and recurse.
        if (!result) {
            Strategy top = stack.pollFirst();
            result = hasNext();
            stack.addFirst(top);
        }
        return result;
    }

    private LinkedList<Strategy> stack;
}
