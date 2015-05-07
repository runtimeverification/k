// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.rewritemachine;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.Multimaps;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.rewritemachine.RHSInstruction.Constructor;
import org.kframework.backend.java.rewritemachine.RHSInstruction.Constructor.ConstructorType;
import org.kframework.backend.java.symbolic.BottomUpVisitor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

public class GenerateRHSInstructions extends BottomUpVisitor {

    private final List<RHSInstruction> rhsSchedule = new ArrayList<>();
    private final TermContext context;

    public GenerateRHSInstructions(TermContext context) {
        this.context = context;
    }

    @Override
    public void visit(BuiltinList node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            int sizeRight = 0;
            for (int i = node.elementsRight().size() - 1; i >= 0; i--) {
                Term k = node.elementsRight().get(i);
                k.accept(this);
                sizeRight++;
            }
            int sizeBase = 0;
            for (int i = node.baseTerms().size() - 1; i >= 0; i--) {
                Term k = node.baseTerms().get(i);
                k.accept(this);
                sizeBase++;
            }
            int sizeLeft = 0;
            for (int i = node.elementsLeft().size() - 1; i >= 0; i--) {
                Term k = node.elementsLeft().get(i);
                k.accept(this);
                sizeLeft++;
            }
            rhsSchedule.add(RHSInstruction.CONSTRUCT(new Constructor(
                    ConstructorType.BUILTIN_LIST, sizeLeft, sizeBase, sizeRight)));
        }
    }

    @Override
    public void visit(BuiltinMap node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            int sizeBase = 0;
            for (Term base : node.baseTerms()) {
                base.accept(this);
                sizeBase++;
            }
            int sizeElem = 0;
            for (Map.Entry<Term, Term> entry : node.getEntries().entrySet()) {
                entry.getValue().accept(this);
                entry.getKey().accept(this);
                sizeElem++;
            }
            rhsSchedule.add(RHSInstruction.CONSTRUCT(new Constructor(
                    ConstructorType.BUILTIN_MAP, sizeElem, sizeBase)));
        }
    }

    @Override
    public void visit(BuiltinSet node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            int sizeBase = 0;
            for (Term base : node.baseTerms()) {
                base.accept(this);
                sizeBase++;
            }
            int sizeElem = 0;
            for (Term elem : node.elements()) {
                elem.accept(this);
                sizeElem++;
            }
            rhsSchedule.add(RHSInstruction.CONSTRUCT(new Constructor(
                    ConstructorType.BUILTIN_SET, sizeElem, sizeBase)));
        }
    }

    @Override
    public void visit(CellCollection node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            int sizeBase = 0;
            for (Term base : node.baseTerms()) {
                base.accept(this);
                sizeBase++;
            }
            List<CellLabel> cellLabels = new ArrayList<>();
            for (Map.Entry<CellLabel, List<CellCollection.Cell>> entry : Multimaps.asMap(node.cells()).entrySet()) {
                for (int i = entry.getValue().size() - 1; i >= 0; i--) {
                    entry.getValue().get(i).content().accept(this);
                    cellLabels.add(entry.getKey());
                }
            }
            Collections.reverse(cellLabels);
            rhsSchedule.add(RHSInstruction.CONSTRUCT(new Constructor(
                    ConstructorType.CELL_COLLECTION, sizeBase, cellLabels)));
        }
    }

    @Override
    public void visit(Hole hole) {
        rhsSchedule.add(RHSInstruction.PUSH(hole));
    }

    @Override
    public void visit(KItem node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            node.kList().accept(this);
            node.kLabel().accept(this);
            rhsSchedule.add(RHSInstruction.CONSTRUCT(
                    new Constructor(ConstructorType.KITEM, node.getSource(), node.getLocation())));
            rhsSchedule.add(RHSInstruction.EVAL);
        }
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        rhsSchedule.add(RHSInstruction.PUSH(kLabelConstant));
    }

    @Override
    public void visit(KLabelFreezer node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            node.term().accept(this);
            rhsSchedule.add(RHSInstruction.CONSTRUCT(
                    new Constructor(ConstructorType.KLABEL_FREEZER)));
        }
    }

    @Override
    public void visit(KList node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            int size = 0;
            if (node.hasFrame()) {
                node.frame().accept(this);
                size++;
            }
            for (int i = node.concreteSize() - 1; i >= 0; i--) {
                Term k = node.get(i);
                k.accept(this);
                size++;
            }
            rhsSchedule.add(RHSInstruction.CONSTRUCT(new Constructor(
                    ConstructorType.KLIST, size)));
        }
    }

    @Override
    public void visit(KSequence node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            int size = 0;
            if (node.hasFrame()) {
                node.frame().accept(this);
                size++;
            }
            for (int i = node.concreteSize() - 1; i >= 0; i--) {
                Term k = node.get(i);
                k.accept(this);
                size++;
            }
            final int size2 = size;
            rhsSchedule.add(RHSInstruction.CONSTRUCT(new Constructor(
                    ConstructorType.KSEQUENCE, size2)));
        }
    }

    @Override
    public void visit(KItemProjection node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            node.term().accept(this);
            rhsSchedule.add(RHSInstruction.CONSTRUCT(new Constructor(
                    ConstructorType.KITEM_PROJECTION, node.kind())));
            rhsSchedule.add(RHSInstruction.PROJECT);
        }
    }

    @Override
    public void visit(KLabelInjection node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            node.term().accept(this);
            rhsSchedule.add(RHSInstruction.CONSTRUCT(
                    new Constructor(ConstructorType.KLABEL_INJECTION)));
        }
    }

    @Override
    public void visit(InjectedKLabel node) {
        if (node.isGround() && node.isNormal()) {
            rhsSchedule.add(RHSInstruction.PUSH(node));
        } else {
            node.injectedKLabel().accept(this);
            rhsSchedule.add(RHSInstruction.CONSTRUCT(
                    new Constructor(ConstructorType.INJECTED_KLABEL)));
        }
    }

    @Override
    public void visit(Token token) {
        rhsSchedule.add(RHSInstruction.PUSH(token));
    }

    @Override
    public void visit(UninterpretedToken token) {
        rhsSchedule.add(RHSInstruction.PUSH(token));
    }

    @Override
    public void visit(Variable variable) {
        rhsSchedule.add(RHSInstruction.SUBST(variable));
    }

    public ImmutableList<RHSInstruction> getInstructions() {
        return ImmutableList.copyOf(rhsSchedule);
    }
}
