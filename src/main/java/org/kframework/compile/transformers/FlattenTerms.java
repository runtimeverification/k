// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.KilProperty;
import org.kframework.compile.utils.MaudeHelper;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Transformer flattening concrete syntax terms to applications of KLabels
 */
@KilProperty.Ensures(KilProperty.NO_CONCRETE_SYNTAX)
public class FlattenTerms extends CopyOnWriteTransformer {
    FlattenKSyntax kTrans;

    public FlattenTerms(Context context) {
        super("Syntax K to Abstract K", context);
        kTrans = new FlattenKSyntax(this, context);
    }

    @Override
    public ASTNode visit(KApp node, Void _)  {
        return kTrans.visitNode(node);
    }

    @Override
    public ASTNode visit(KSequence node, Void _)  {
        return kTrans.visitNode(node);
    }

    @Override
    public ASTNode visit(Variable node, Void _)  {
        if (node.getSort().isComputationSort() && !node.isFreshConstant())
            return kTrans.visitNode(node);
        return node;
    }

    @Override
    public ASTNode visit(ListTerminator node, Void _)  {
        if (node.getSort().isComputationSort())
            return kTrans.visitNode(node);
        return node;
    }

    /**
     * Flattens this TermCons if it has sort K, KItem, or any sort other than
     * those defined in {@link org.kframework.kil.Sort}.
     */
    @Override
    public ASTNode visit(TermCons tc, Void _) {
        if (tc.getSort().isComputationSort())
            return kTrans.visitNode(tc);
        return super.visit(tc, _);
    }

    @Override
    public ASTNode visit(Constant constant, Void _) {
        return kTrans.visitNode(constant);
    }

    class FlattenKSyntax extends CopyOnWriteTransformer {
        FlattenTerms trans;

        public FlattenKSyntax(FlattenTerms t, Context context) {
            super("Flatten K Syntax", context);
            trans = t;
        }

        @Override
        public ASTNode complete(ASTNode node, ASTNode r) {
            r.copyAttributesFrom(node);
            return super.complete(node, r);
        }

        @Override
        public ASTNode visit(KApp node, Void _)  {
            Term label = (Term) trans.visitNode(node.getLabel());
            Term child = (Term) trans.visitNode(node.getChild());
            if (child != node.getChild() || label != node.getLabel()) {
                node = node.shallowCopy();
                node.setChild(child);
                node.setLabel(label);
            }
            return node;
        }

        @Override
        public ASTNode visit(Freezer node, Void _)  {
            return KApp.of(new FreezerLabel((Term) this.visitNode(node.getTerm())));
        }

        @Override
        public ASTNode visit(Constant constant, Void _) {
            Term rez;
            if (constant.getSort().equals(Sort.KLABEL)) {
                rez = new KLabelConstant(constant.getValue());
            } else {
                // builtin token or lexical token
                rez =  Token.kAppOf(constant.getSort(), constant.getValue());
            }
            rez.setLocation(constant.getLocation());
            rez.setSource(constant.getSource());
            rez.copyAttributesFrom(constant);

            return this.visitNode(rez);
        }

        @Override
        public ASTNode visit(TermCons tc, Void _)  {
            if (!tc.getSort().isComputationSort()) {
                return KApp.of(new KInjectedLabel((Term) trans.visitNode(tc)));
            }

            Location l = tc.getLocation();
            Source s = tc.getSource();
            Production ppp = tc.getProduction();
            KList lok = new KList(l, s);
            for (Term t : tc.getContents()) {
                lok.getContents().add((Term) this.visitNode(t));
            }
            String label;
            if (tc.isListTerminator())
                label = tc.getProduction().getTerminatorKLabel();
            else
                label = ppp.getKLabel();
            return new KApp(l, s, KLabelConstant.of(label, context), lok);
        }

        @Override
        public ASTNode visit(KLabel kLabel, Void _)  {
            return new KApp(
                    kLabel.getLocation(),
                    kLabel.getSource(),
                    new KInjectedLabel(kLabel),
                    KList.EMPTY);
        }

        @Override
        public ASTNode visit(ListTerminator emp, Void _) {
            Location l = emp.getLocation();
            Source f = emp.getSource();
            if (!emp.getSort().isComputationSort()) {
                return KApp.of(new KInjectedLabel(emp));
            }
            // if this is a list sort
            if (!MaudeHelper.isBasicSort(emp.getSort())) {
                Production listProd = context.listProductions.get(emp.getSort());
                return new KApp(l, f, KLabelConstant.of(listProd.getTerminatorKLabel(), context), KList.EMPTY);
            }
            return emp;
        }

        @Override
        public ASTNode visit(Collection node, Void _)  {
            if (node instanceof KSequence)
                return super.visit(node, _);
            return KApp.of(new KInjectedLabel((Term) trans.visitNode(node)));
        }

        @Override
        public ASTNode visit(CollectionItem node, Void _)  {
            return KApp.of(new KInjectedLabel((Term) trans.visitNode(node)));
        }

        @Override
        public ASTNode visit(CollectionBuiltin node, Void _)  {
            throw new AssertionError("should always flatten before compiling data structures");
        }

        @Override
        public ASTNode visit(MapBuiltin node, Void _)  {
            throw new AssertionError("should always flatten before compiling data structures");
        }

        @Override
        public ASTNode visit(Cell node, Void _)  {
            return KApp.of(new KInjectedLabel((Term) trans.visitNode(node)));
        }

        @Override
        public ASTNode visit(Variable node, Void _)  {
            if (node.isFreshConstant()) return node;
            if (node.getSort().equals(Sort.KITEM) || node.getSort().equals(Sort.K)) {
                return node;
            }
            if (node.getSort().isKSort()) {
                return KApp.of(new KInjectedLabel(node));
            }

            if (node.getSort().equals(Sort.BUILTIN_BOOL)
                    || node.getSort().equals(Sort.BUILTIN_INT)
                    || node.getSort().equals(Sort.BUILTIN_FLOAT)
                    || node.getSort().equals(Sort.BUILTIN_STRING)) {
                return node;
            }

            if (context.getDataStructureSorts().containsKey(node.getSort())) {
                //node = node.shallowCopy();
                //node.setSort(context.dataStructureSorts.get(node.getSort()).type());
                //return KApp.of(new KInjectedLabel(node));
                return node;
            }

            node = node.shallowCopy();
            return node;
        }
    }
}
