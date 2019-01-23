// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.*;
import org.kframework.backend.java.kil.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Combines a list of {@code LocalVisitor}s.
 *
 * @author Traian
 */
public class CombinedLocalVisitor extends LocalVisitor {

    final List<LocalVisitor> Visitors;

    public CombinedLocalVisitor() {
        Visitors = new ArrayList<>();
    }

    public CombinedLocalVisitor(LocalVisitor... localVisitors) {
        this();
        Visitors.addAll(Arrays.asList(localVisitors));
    }

    public void addVisitor(LocalVisitor t) {
        Visitors.add(t);
    }

    @Override
    public String getName() {
        String name = "Combined Visitor:\n";
        for (Visitor t : Visitors) {
            name += "\t" + t.getName() + "\n";
        }
        return name;
    }

    /**
     * Invokes all internal visitors on the given node in order.
     *
     * @param node
     *            the given node
     */
    private void visitAll(JavaSymbolicObject node) {
        for (LocalVisitor t : Visitors) {
            t.resetProceed();
            node.accept(t);
            proceed &= t.isProceed();
            if (!proceed) return;
        }
    }

    @Override
    public void visit(BitVector node) {
        visitAll(node);
    }

    @Override
    public void visit(BoolToken node) {
        visitAll(node);
    }

    @Override
    public void visit(BuiltinList node) {
        visitAll(node);
    }

    @Override
    public void visit(BuiltinMap node) {
        visitAll(node);
    }

    @Override
    public void visit(BuiltinSet node) {
        visitAll(node);
    }

    @Override
    public void visit(Collection node) {
        visitAll(node);
    }

    @Override
    public void visit(ConstrainedTerm node) {
        visitAll(node);
    }

    @Override
    public void visit(Hole node) {
        visitAll(node);
    }

    @Override
    public void visit(IntToken node) {
        visitAll(node);
    }

    @Override
    public void visit(KLabelConstant node) {
        visitAll(node);
    }

    @Override
    public void visit(KLabelInjection node) {
        visitAll(node);
    }

    @Override
    public void visit(KItem node) {
        visitAll(node);
    }

    @Override
    public void visit(KCollection node) {
        visitAll(node);
    }

    @Override
    public void visit(KLabel node) {
        visitAll(node);
    }

    @Override
    public void visit(KList node) {
        visitAll(node);
    }

    @Override
    public void visit(KSequence node) {
        visitAll(node);
    }

    @Override
    public void visit(MetaVariable node) {
        visitAll(node);
    }

    @Override
    public void visit(Rule node) {
        visitAll(node);
    }

    @Override
    public void visit(ConjunctiveFormula node) {
        visitAll(node);
    }

    @Override
    public void visit(DisjunctiveFormula node) {
        visitAll(node);
    }

    @Override
    public void visit(Term node) {
        visitAll(node);
    }

    @Override
    public void visit(Token node) {
        visitAll(node);
    }

    @Override
    public void visit(UninterpretedToken node) {
        visitAll(node);
    }

    @Override
    public void visit(Variable node) {
        visitAll(node);
    }
}
