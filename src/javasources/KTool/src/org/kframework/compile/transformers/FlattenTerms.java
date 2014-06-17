// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.KilProperty;
import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Collection;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.krun.K;
import org.kframework.utils.StringUtil;

import java.util.*;

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
        if (MetaK.isComputationSort(node.getSort()) && !node.isFreshConstant())
            return kTrans.visitNode(node);
        return node;
    }

    @Override
    public ASTNode visit(ListTerminator node, Void _)  {
        if (MetaK.isComputationSort(node.getSort()))
            return kTrans.visitNode(node);
        return node;
    }

    /**
     * Flattens this TermCons if it has sort K, KItem, or any sort other than
     * those defined in {@link org.kframework.kil.KSort}.
     */
    @Override
    public ASTNode visit(TermCons tc, Void _)  {
        if (MetaK.isComputationSort(tc.getSort()))
            return kTrans.visitNode(tc);
        return super.visit(tc, _);
    }

    class FlattenKSyntax extends CopyOnWriteTransformer {
        FlattenTerms trans;

        public FlattenKSyntax(FlattenTerms t, Context context) {
            super("Flatten K Syntax", context);
            trans = t;
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
        public ASTNode visit(TermCons tc, Void _)  {
            if (!MetaK.isComputationSort(tc.getSort())) {
                return KApp.of(new KInjectedLabel((Term) trans.visitNode(tc)));
            }

            String l = tc.getLocation();
            String f = tc.getFilename();
            Production ppp = tc.getProduction();
            KList lok = new KList(l, f);
            for (Term t : tc.getContents()) {
                lok.getContents().add((Term) this.visitNode(t));
            }
            String label;
            if (tc.isListTerminator())
                label = tc.getProduction().getListDecl().getTerminatorKLabel();
            else
                label = ppp.getKLabel();
            return new KApp(l, f, KLabelConstant.of(label, context), lok);
        }

        @Override
        public ASTNode visit(KLabel kLabel, Void _)  {
            return new KApp(
                    kLabel.getLocation(),
                    kLabel.getFilename(),
                    new KInjectedLabel(kLabel),
                    KList.EMPTY);
        }

        @Override
        public ASTNode visit(ListTerminator emp, Void _) {
            String l = emp.getLocation();
            String f = emp.getFilename();
            if (!MetaK.isComputationSort(emp.getSort())) {
                return KApp.of(new KInjectedLabel(emp));
            }
            // if this is a list sort
            if (!MaudeHelper.basicSorts.contains(emp.getSort())) {
                Production listProd = context.listConses.get(emp.getSort());
                String separator = ((UserList) listProd.getItems().get(0)).getSeparator();
                return new KApp(l, f, KLabelConstant.of(MetaK.getListUnitLabel(separator), context), KList.EMPTY);
                // Constant cst = new Constant(l, f, KSorts.KLABEL, "'." + emp.getSort() + "");
                // return new KApp(l, f, cst, new Empty(l, f, MetaK.Constants.KList));
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
        public ASTNode visit(MapItem node, Void _)  {
            return KApp.of(new KInjectedLabel((Term) trans.visitNode(node)));
        }

        @Override
        public ASTNode visit(CollectionBuiltin node, Void _)  {
            /* just for LHS for now */
            assert (node.isLHSView() || node.isElementCollection());

            LinkedHashSet<Term> elements = new LinkedHashSet<>(node.elements().size());
            for (Term term : node.elements()) {
                Term transformedTerm = (Term) trans.visitNode(term);
                elements.add(transformedTerm);
            }

            ArrayList<Term> terms = new ArrayList<>(node.baseTerms().size());
            if (node.isLHSView()) {
                Variable frame = node.viewBase();
                frame.setSort(node.sort().type());
                terms.add(frame);
            }

            return KApp.of(new KInjectedLabel(CollectionBuiltin.of(
                    node.sort(),
                    terms,
                    elements)));
        }

        @Override
        public ASTNode visit(MapBuiltin node, Void _)  {
            /* just for LHS for now */
            assert (node.isLHSView() || node.isElementCollection());

            LinkedHashMap<Term, Term> elements = new LinkedHashMap<>(node.elements().size());
            for (java.util.Map.Entry<Term, Term> entry : node.elements().entrySet()) {
                Term transformedKey = (Term) trans.visitNode(entry.getKey());
                Term transformedValue = (Term) trans.visitNode(entry.getValue());
                elements.put(transformedKey, transformedValue);
            }

            ArrayList<Term> terms = new ArrayList<>(node.baseTerms().size());
            if (node.isLHSView()) {
                Variable frame = node.viewBase();
                frame.setSort(node.sort().type());
                terms.add(frame);
            }

            return KApp.of(new KInjectedLabel(new MapBuiltin(
                    node.sort(),
                    terms,
                    elements)));
        }

        @Override
        public ASTNode visit(Cell node, Void _)  {
            return KApp.of(new KInjectedLabel((Term) trans.visitNode(node)));
        }

        @Override
        public ASTNode visit(Variable node, Void _)  {
            if (node.isFreshConstant()) return node;
            if (node.getSort().equals(KSorts.KITEM) || node.getSort().equals(KSorts.K)) {
                return node;
            }
            if (MetaK.isKSort(node.getSort())) {
                return KApp.of(new KInjectedLabel(node));
            }

            if (node.getSort().equals(BoolBuiltin.SORT_NAME)
                    || node.getSort().equals(IntBuiltin.SORT_NAME)
                    || node.getSort().equals(FloatBuiltin.SORT_NAME)
                    || node.getSort().equals(StringBuiltin.SORT_NAME)) {
                return node;
            }

            if (context.getDataStructureSorts().containsKey(node.getSort())) {
                //node = node.shallowCopy();
                //node.setSort(context.dataStructureSorts.get(node.getSort()).type());
                //return KApp.of(new KInjectedLabel(node));
                return node;
            }

            node = node.shallowCopy();
            if (kompileOptions.backend.java() || K.backend.equals("java")) {
                /* the Java Rewrite Engine preserves sort information for variables */
            } else {
                node.setSort(KSorts.KITEM);
            }
            return node;
        }
    }
}
