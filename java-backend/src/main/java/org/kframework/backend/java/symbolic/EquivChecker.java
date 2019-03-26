// Copyright (c) 2016-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.ConstrainedTerm;
import org.kframework.backend.java.util.FormulaContext;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by daejunpark on 8/15/16.
 */
public class EquivChecker {

    public static boolean equiv(
            java.util.List<ConstrainedTerm> startSyncNodes1,
            java.util.List<ConstrainedTerm> startSyncNodes2,
            java.util.List<ConstrainedTerm> targetSyncNodes1,
            java.util.List<ConstrainedTerm> targetSyncNodes2,
            java.util.List<ConjunctiveFormula> startEnsures,
            java.util.List<ConjunctiveFormula> targetEnsures,
            java.util.List<Boolean> trusted1,
            java.util.List<Boolean> trusted2,
            //
            SymbolicRewriter rewriter1,
            SymbolicRewriter rewriter2
    ) {

        assert startEnsures.size() == targetEnsures.size();
        assert targetSyncNodes1.size() == targetEnsures.size();
        assert targetSyncNodes2.size() == targetEnsures.size();

        int numSyncPoints = targetEnsures.size();

        java.util.List<Set<SyncNode>> allSyncNodes1 = newListOfSets(numSyncPoints);
        java.util.List<Set<SyncNode>> allSyncNodes2 = newListOfSets(numSyncPoints);

        // start with non-final nodes
        java.util.List<SyncNode> currSyncNodes1 = new ArrayList<>();
        java.util.List<SyncNode> currSyncNodes2 = new ArrayList<>();
        for (int i = 0; i < numSyncPoints; i++) {
            if (trusted1.get(i)) { assert trusted2.get(i); continue; }

            ConstrainedTerm t1 = startSyncNodes1.get(i);
            ConstrainedTerm t2 = startSyncNodes2.get(i);

            /* TODO: should final nodes be trusted?
            List<ConstrainedTerm> nt1 = rewriter1.fastComputeRewriteStep(t1, false, true, true);
            List<ConstrainedTerm> nt2 = rewriter2.fastComputeRewriteStep(t2, false, true, true);
            assert nt1.isEmpty() == nt2.isEmpty();
            if (nt1.isEmpty()) continue;
             */

            currSyncNodes1.add(new SyncNode(i, null, t1, null)); // TODO: check if null is safe
            currSyncNodes2.add(new SyncNode(i, null, t2, null));
        }

        while (!currSyncNodes1.isEmpty() && !currSyncNodes2.isEmpty()) {

            java.util.List<Set<SyncNode>> nextSyncNodes1 = getNextSyncNodes(currSyncNodes1, targetSyncNodes1, rewriter1);
            java.util.List<Set<SyncNode>> nextSyncNodes2 = getNextSyncNodes(currSyncNodes2, targetSyncNodes2, rewriter2);

            // fail
            if (nextSyncNodes1 == null || nextSyncNodes2 == null) return false; // TODO: output more information for failure

            allSyncNodes1 = mergeListOfSets(allSyncNodes1, nextSyncNodes1);
            allSyncNodes2 = mergeListOfSets(allSyncNodes2, nextSyncNodes2);

            matchSyncNodes(allSyncNodes1, allSyncNodes2, startEnsures, targetEnsures);
            validateSyncNodes(allSyncNodes1);
            validateSyncNodes(allSyncNodes2);

            currSyncNodes1.clear();
            currSyncNodes2.clear();
            for (int i = 0; i < numSyncPoints; i++) {
                for (SyncNode node : allSyncNodes1.get(i)) {
                    if (node.mark == Mark.RED) {
                        currSyncNodes1.add(node);
                    }
                }
                for (SyncNode node : allSyncNodes2.get(i)) {
                    if (node.mark == Mark.RED) {
                        currSyncNodes2.add(node);
                    }
                }
            }

            if (currSyncNodes1.isEmpty() != currSyncNodes2.isEmpty()) {
                return false; // TODO: output more information for failure
            }
        }

        return true;
    }

    public static java.util.List<Set<SyncNode>> getNextSyncNodes(
            java.util.List<SyncNode> currSyncNodes,
            java.util.List<ConstrainedTerm> targetSyncNodes,
            //
            SymbolicRewriter rewriter
    ) {
        int numSyncPoints = targetSyncNodes.size();
        java.util.List<Set<SyncNode>> nextSyncNodes = newListOfSets(numSyncPoints);
        for (SyncNode currSyncNode : currSyncNodes) {
            java.util.List<Set<SyncNode>> nodes = getNextSyncNodes(currSyncNode, targetSyncNodes, rewriter);
            if (nodes == null) return null; // failed // TODO: output more information for failure
            nextSyncNodes = mergeListOfSets(nextSyncNodes, nodes);
        }
        return nextSyncNodes;
    }

    public static java.util.List<Set<SyncNode>> getNextSyncNodes(
            SyncNode currSyncNode,
            java.util.List<ConstrainedTerm> targetSyncNodes,
            //
            SymbolicRewriter rewriter
    ) {
        int numSyncPoints = targetSyncNodes.size();

        java.util.List<Set<SyncNode>> nextSyncNodes = newListOfSets(numSyncPoints);

        java.util.List<ConstrainedTerm> queue = new ArrayList<>();
        java.util.List<ConstrainedTerm> nextQueue = new ArrayList<>();

        ConstrainedTerm initTerm = currSyncNode.currSyncNode;
        queue.add(initTerm);

        int steps = 0;
        while (!queue.isEmpty()) {
            ++steps;
            for (ConstrainedTerm curr : queue) {

                java.util.List<ConstrainedTerm> nexts = rewriter.fastComputeRewriteStep(curr, false, true, true, steps,
                        initTerm);

                if (nexts.isEmpty()) {
                    /* final term */
                    return null; // failed // TODO: output more information for failure
                }

            loop:
                for (ConstrainedTerm next : nexts) {
                    for (int i = 0; i < numSyncPoints; i++) {
                        ConjunctiveFormula constraint = next.matchImplies(targetSyncNodes.get(i), true, false,
                                new FormulaContext(FormulaContext.Kind.EquivImplication, null, next.termContext().global()), null);
                        if (constraint != null) {
                            SyncNode node = new SyncNode(currSyncNode.startSyncPoint, currSyncNode, next, constraint);
                            nextSyncNodes.get(i).add(node);
                            continue loop;
                        }
                    }
                    nextQueue.add(next);
                }
            }

            /* swap the queues */
            java.util.List<ConstrainedTerm> temp;
            temp = queue;
            queue = nextQueue;
            nextQueue = temp;
            nextQueue.clear();
        }

        return nextSyncNodes;
    }

    public static void matchSyncNodes(
            java.util.List<Set<SyncNode>> syncNodes1,
            java.util.List<Set<SyncNode>> syncNodes2,
            java.util.List<ConjunctiveFormula> startEnsures,
            java.util.List<ConjunctiveFormula> targetEnsures) {

        assert startEnsures.size() == targetEnsures.size();
        assert syncNodes1.size() == targetEnsures.size();
        assert syncNodes2.size() == targetEnsures.size();

        int numSyncPoints = targetEnsures.size();

        for (int i = 0; i < numSyncPoints; i++) {
            for (SyncNode ct1 : syncNodes1.get(i)) {
                for (SyncNode ct2 : syncNodes2.get(i)) {
                    if (ct1.startSyncPoint != ct2.startSyncPoint) continue;
                    if (ct1.mark == Mark.BLACK && ct2.mark == Mark.BLACK) continue;
                    ConjunctiveFormula c1 = ConjunctiveFormula.of(ct1.constraint);
                    ConjunctiveFormula c2 = ConjunctiveFormula.of(ct2.constraint);
                    ConjunctiveFormula c0 = ConjunctiveFormula.of(startEnsures.get(ct1.startSyncPoint));
                    ConjunctiveFormula e = ConjunctiveFormula.of(targetEnsures.get(i));
                    ConjunctiveFormula c = c1.add(c2).add(c0).simplify(); // TODO: termContext ??
                    if (!c.isFalse() && !c.checkUnsat(new FormulaContext(FormulaContext.Kind.EquivConstr, null, c.globalContext()))
                            && c.smartImplies(e) /* c.implies(e, Collections.emptySet()) */) {
                        ct1.mark = Mark.BLACK;
                        ct2.mark = Mark.BLACK;
                    }
                }
            }
        }
    }

    public static void validateSyncNodes(java.util.List<Set<SyncNode>> syncNodes) {
        // TODO: implement more efficiently

        // mark grey for invalid nodes
        boolean changed = true;
        while (changed) {
            changed = false;
            for (Set<SyncNode> ssn : syncNodes) {
                for (SyncNode sn : ssn) {
                    if (sn.prevSyncNode.mark == Mark.BLACK || sn.prevSyncNode.mark == Mark.GREY) {
                        switch (sn.mark) {
                        case BLACK:
                            assert false; // TODO: what happend?
                            break;
                        case RED:
                            sn.mark = Mark.GREY;
                            changed = true;
                            break;
                        case GREY:
                            break;
                        }
                    }
                }
            }
        }

        // sweep grey nodes
        for (int i = 0; i < syncNodes.size(); i++) {
            Set<SyncNode> set = syncNodes.get(i).stream()
                    .filter(n -> n.mark != Mark.GREY)
                    .collect(Collectors.toSet());
            syncNodes.set(i, set);
        }
    }

    public static java.util.List<Set<SyncNode>> newListOfSets(int size) {
        java.util.List<Set<SyncNode>> list = new ArrayList<>();
        for (int i = 0; i < size; i++) {
            list.add(new HashSet<SyncNode>());
        }
        return list;
    }

    public static java.util.List<Set<SyncNode>> mergeListOfSets(
            java.util.List<Set<SyncNode>> to,
            java.util.List<Set<SyncNode>> from
    ) {
        assert to.size() == from.size();
        for (int i = 0; i < to.size(); i++) {
            to.get(i).addAll(from.get(i));
        }
        return to;
    }

    private static class SyncNode {
        public int startSyncPoint;
        public SyncNode prevSyncNode;
        public ConstrainedTerm currSyncNode;
        public ConjunctiveFormula constraint;
        public Mark mark;

        public SyncNode(
                int startSyncPoint,
                SyncNode prevSyncNode,
                ConstrainedTerm currSyncNode,
                ConjunctiveFormula constraint
        ) {
            this.startSyncPoint = startSyncPoint;
            this.prevSyncNode = prevSyncNode;
            this.currSyncNode = currSyncNode;
            this.constraint = constraint;
            this.mark = Mark.RED;
        }
    }

    private enum Mark {
        RED,    // not matched yet
        BLACK,  // matched
        GREY    // invalid; its parent was matched later
    }


}
