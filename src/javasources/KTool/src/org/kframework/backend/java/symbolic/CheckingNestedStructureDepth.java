// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.Production;

/**
 * Checks that the depth of certain nested structures should not exceed some
 * given limits.
 *
 * @author YilongL
 *
 */
public class CheckingNestedStructureDepth implements KastStructureCheckerPlugin {

    private final Map<Sort, Integer> nestedLevelOfSort = new HashMap<Sort, Integer>();
    private final Map<Sort, Integer> maxNestedLevelOfSort = new HashMap<Sort, Integer>();

    private final LocalVisitor preVisitor = new IncNestedLevelOfSort();
    private final LocalVisitor postVisitor = new DecNestedLevelOfSort();
    private PluggableKastStructureChecker checker;

    public CheckingNestedStructureDepth() {
        // TODO(YilongL): handle user-specified depth properly
        this.setMaxNestedLevelOf(Sort.of("AExp"), 2);
        this.setMaxNestedLevelOf(Sort.of("BExp"), 1);
        this.setMaxNestedLevelOf(Sort.of("Block"), 2);
    }

    @Override
    public void registerTo(PluggableKastStructureChecker checker) {
        assert this.checker == null;
        this.checker = checker;
    }

    @Override
    public void reset() {
        nestedLevelOfSort.clear();
        preVisitor.resetProceed();
        postVisitor.resetProceed();
    }

    @Override
    public LocalVisitor getPreVisitor() {
        return preVisitor;
    }

    @Override
    public LocalVisitor getPostVisitor() {
        return postVisitor;
    }

    public void setMaxNestedLevelOf(Sort sort, int level) {
        maxNestedLevelOfSort.put(sort, level);
    }

    private static final Map<KLabelConstant, Set<Sort>> cachedSortsOfKLabel = new HashMap<>();

    private Set<Sort> computeSortsOf(KLabelConstant kLabel) {
        Set<Sort> sorts = cachedSortsOfKLabel.get(kLabel);
        if (sorts == null) {
            Set<Sort> set = new HashSet<>();
            // TODO(YilongL): there could be multiple productions generating a
            // same KLabelConstant, thus multiple sorts; need to find the
            // correct or the most concrete sort!
//            assert kLabel.productions().size() == 1 : "TODO(YilongL): fix it";
            for (Production prod : kLabel.productions()) {
                set.add(Sort.of(prod.getSort()));
            }
            cachedSortsOfKLabel.put(kLabel, set);
            sorts = set;
        }
        return sorts;
    }

    private class IncNestedLevelOfSort extends LocalVisitor {
        @Override
        public void visit(KItem kItem) {
            // TODO(AndreiS): deal with KLabel variables
            if (!(kItem.kLabel() instanceof KLabelConstant)) {
                return;
            }

            KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();
            for (Sort sort : computeSortsOf(kLabel)) {
                check(sort);
            }
        }

        @Override
        public void visit(Variable variable) {
            check(variable.sort());
        }

        private void check(Sort sort) {
            if (nestedLevelOfSort.get(sort) == null) {
                nestedLevelOfSort.put(sort, 0);
            }

            int depth = nestedLevelOfSort.get(sort) + 1;
            Integer maxDepth = maxNestedLevelOfSort.get(sort);
            if ((maxDepth != null) && (depth > maxDepth)) {
                this.proceed = false;
                checker.flagFailure(CheckingNestedStructureDepth.this);
                return;
            } else {
                nestedLevelOfSort.put(sort, depth);
            }
        }
    }

    private class DecNestedLevelOfSort extends LocalVisitor {
        @Override
        public void visit(KItem kItem) {
            // TODO(AndreiS): deal with KLabel variables
            if (!(kItem.kLabel() instanceof KLabelConstant)) {
                return;
            }

            KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();
            for (Sort sort : computeSortsOf(kLabel)) {
                nestedLevelOfSort.put(sort, nestedLevelOfSort.get(sort) - 1);
            }
        }

        @Override
        public void visit(Variable variable) {
            nestedLevelOfSort.put(variable.sort(), nestedLevelOfSort.get(variable.sort()) - 1);
        }
    }
}
