// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BitVector;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.*;


public class BasicVisitor implements Visitor {

    public void visitNode(JavaSymbolicObject node) {
        if (node instanceof KItem) {
            visit((KItem) node);
        } else if (node instanceof KLabelConstant) {
            visit((KLabelConstant) node);
        } else if (node instanceof KList) {
            visit((KList) node);
        } else if (node instanceof KSequence) {
            visit((KSequence) node);
        } else if (node instanceof CellCollection) {
            visit((CellCollection) node);
        } else if (node instanceof Variable) {
            visit((Variable) node);
        } else if (node instanceof BoolToken) {
            visit((BoolToken) node);
        } else if (node instanceof IntToken) {
            visit((IntToken) node);
        } else if (node instanceof FloatToken) {
            visit((FloatToken) node);
        } else if (node instanceof StringToken) {
            visit((StringToken) node);
        } else if (node instanceof BitVector) {
            visit((BitVector) node);
        } else if (node instanceof UninterpretedToken) {
            visit((UninterpretedToken) node);
        } else if (node instanceof BuiltinList) {
            visit((BuiltinList) node);
        } else if (node instanceof BuiltinMap) {
            visit((BuiltinMap) node);
        } else if (node instanceof BuiltinSet) {
            visit((BuiltinSet) node);
        } else if (node instanceof ConjunctiveFormula) {
            visit((ConjunctiveFormula) node);
        } else if (node instanceof DisjunctiveFormula) {
            visit((DisjunctiveFormula) node);
        } else if (node instanceof KLabelInjection) {
            visit((KLabelInjection) node);
        } else if (node instanceof KItemProjection) {
            visit((KItemProjection) node);
        } else if (node instanceof InjectedKLabel) {
            visit((InjectedKLabel) node);
        } else if (node instanceof Hole) {
            visit((Hole) node);
        } else if (node instanceof MetaVariable) {
            visit((MetaVariable) node);
        } else if (node instanceof ConstrainedTerm) {
            visit((ConstrainedTerm) node);
        } else if (node instanceof Rule) {
            visit((Rule) node);
        } else if (node instanceof Bottom) {
            visit((Bottom) node);
        } else if (node instanceof RuleAutomatonDisjunction) {
            visit((RuleAutomatonDisjunction) node);
        } else if (node instanceof InnerRHSRewrite) {
            visit((InnerRHSRewrite) node);
        } else {
            assert false : "unexpected class " + node.getClass();
        }
    }

    @Override
    public String getName() {
        return this.getClass().toString();
    }

    @Override
    public void visit(BitVector bitVector) {
        visit((Token) bitVector);
    }

    @Override
    public void visit(BoolToken boolToken) {
        visit((Token) boolToken);
    }

    public void visit(Bottom bottom) {
        visit((Term) bottom);
    }

    @Override
    public void visit(BuiltinList node) {
        node.elementsLeft().stream().forEach(this::visitNode);
        node.baseTerms().stream().forEach(this::visitNode);
        node.elementsRight().stream().forEach(this::visitNode);
    }

    @Override
    public void visit(BuiltinMap builtinMap) {
        builtinMap.getEntries().entrySet().stream().forEach(e -> {
            visitNode(e.getKey());
            visitNode(e.getValue());
        });
        builtinMap.baseTerms().stream().forEach(this::visitNode);
        visit((Collection) builtinMap);
    }

    @Override
    public void visit(BuiltinSet builtinSet) {
        builtinSet.elements().stream().forEach(this::visitNode);
        builtinSet.baseTerms().stream().forEach(this::visitNode);
        visit((Collection) builtinSet);
    }

    @Override
    public void visit(CellCollection cellCollection) {
        cellCollection.cells().values().stream().forEach(c -> visitNode(c.content()));
        cellCollection.baseTerms().stream().forEach(this::visitNode);
        visit((Collection) cellCollection);
    }

    @Override
    public void visit(Collection collection) {
        visit((Term) collection);
    }

    @Override
    public void visit(ConstrainedTerm constrainedTerm) {
        visitNode(constrainedTerm.term());
        visitNode(constrainedTerm.constraint());
    }

    @Override
    public void visit(Hole hole) {
        visit((Term) hole);
    }

    @Override
    public void visit(IntToken intToken) {
        visit((Token) intToken);
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        visit((KLabel) kLabelConstant);
    }

    @Override
    public void visit(KLabelFreezer kLabelFreezer) {
        visitNode(kLabelFreezer.term());
        visit((KLabelInjection) kLabelFreezer);
    }

    @Override
    public void visit(KLabelInjection kLabelInjection) {
        visitNode(kLabelInjection.term());
        visit((KLabel) kLabelInjection);
    }

    @Override
    public void visit(KItem kItem) {
        visitNode(kItem.kLabel());
        visitNode(kItem.kList());
        visit((Term) kItem);
    }

    @Override
    public void visit(KItemProjection kItemProjection) {
        visitNode(kItemProjection.term());
        visit((Term) kItemProjection);
    }

    @Override
    public void visit(InjectedKLabel injectedKLabel) {
        visitNode(injectedKLabel.injectedKLabel());
        visit((Term) injectedKLabel);
    }

    @Override
    public void visit(RuleAutomatonDisjunction ruleAutomatonDisjunction) {
        ruleAutomatonDisjunction.disjunctions().stream().map(p -> p.getLeft()).forEach(this::visitNode);
    }

    @Override
    public void visit(InnerRHSRewrite innerRHSRewrite) {
    }

    @Override
    public void visit(KCollection kCollection) {
        kCollection.getContents().stream().forEach(this::visitNode);
        if (kCollection.hasFrame()) {
            visitNode(kCollection.frame());
        }
        visit((Collection) kCollection);
    }

    @Override
    public void visit(KLabel kLabel) {
        visit((Term) kLabel);
    }

    @Override
    public void visit(KList kList) {
        visit((KCollection) kList);
    }

    @Override
    public void visit(KSequence kSequence) {
        visit((KCollection) kSequence);
    }

    @Override
    public void visit(MetaVariable metaVariable) {
        visit((Token) metaVariable);
    }

    @Override
    public void visit(Rule rule) {
        visitNode(rule.leftHandSide());
        visitNode(rule.rightHandSide());
        visitNode(rule.lookups());
        rule.requires().stream().forEach(this::visitNode);
        rule.ensures().stream().forEach(this::visitNode);
        rule.freshConstants().stream().forEach(this::visitNode);
    }

    @Override
    public void visit(ConjunctiveFormula conjunctiveFormula) {
        conjunctiveFormula.substitution().entrySet().stream().forEach(e -> {
            visitNode(e.getKey());
            visitNode(e.getValue());
        });
        conjunctiveFormula.equalities().stream().forEach(e -> {
            visitNode(e.leftHandSide());
            visitNode(e.rightHandSide());
        });
        conjunctiveFormula.disjunctions().stream().forEach(this::visitNode);
    }

    @Override
    public void visit(DisjunctiveFormula disjunctiveFormula) {
        disjunctiveFormula.conjunctions().stream().forEach(this::visitNode);
    }

    @Override public void visit(Term term) { }

    @Override
    public void visit(Token token) {
        visit((Term) token);
    }

    @Override
    public void visit(UninterpretedToken uninterpretedToken) {
        visit((Term) uninterpretedToken);
    }

    @Override
    public void visit(Variable variable) {
        visit((Term) variable);
    }

}
