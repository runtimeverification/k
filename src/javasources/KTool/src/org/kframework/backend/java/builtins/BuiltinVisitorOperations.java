package org.kframework.backend.java.builtins;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.LocalTransformer;
import org.kframework.backend.java.symbolic.PrePostTransformer;
import org.kframework.kil.ASTNode;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Traian
 */
public class BuiltinVisitorOperations {


    static class BuiltinVisitor extends PrePostTransformer {

        private List<Term> guardParams;
        private List<Term> visitParams;
        private KLabel ifLabel;
        private KLabel visitLabel;

        BuiltinVisitor(TermContext context, KLabel guardLabel, List<Term> guardParams, KLabel visitLabel, List<Term> visitParams) {
            super(context);
            this.guardParams = guardParams;
            this.visitParams = visitParams;
            this.ifLabel = guardLabel;
            this.visitLabel = visitLabel;
            this.preTransformer.addTransformer(new TermVisitor(context));
        }

        private class TermVisitor extends LocalTransformer {
            private TermVisitor(TermContext context) {
                super(context);
            }

            @Override
            public ASTNode transform(Term node) {
                guardParams.set(0, node);
                KItem test = new KItem(ifLabel, new KList(ImmutableList.copyOf(guardParams)), context.definition().context());
                Term truth = test.evaluate(context);
                //TODO:  Think about what happens when test has syumbolic values in it.
                if (!(truth instanceof BoolToken)) return node;
                if (!((BoolToken) truth).booleanValue()) return node;
                visitParams.set(0, node);
                node = new KItem(visitLabel, new KList(ImmutableList.copyOf(visitParams)), context.definition().context());
                node = node.evaluate(context);
                return new DoneTransforming(node);
            }
        }
    }

    public static Term injectedTerm(Term kItem) {
        assert kItem instanceof KItem;
        KLabel kLabel = ((KItem) kItem).kLabel();
        assert kLabel instanceof KLabelInjection;
        final KLabelInjection kLabelInjection = (KLabelInjection) kLabel;
        return kLabelInjection.term();
    }

    public static KLabel injectedKLabel(Term kItem) {
        Term labelTerm = injectedTerm(kItem);
        assert labelTerm instanceof KLabel;
        return (KLabel) labelTerm;
    }

     public static KList injectedKList(Term kItem) {
        Term listTerm = injectedTerm(kItem);
        assert listTerm instanceof KList;
        return (KList) listTerm;
    }

    //public static Term visit(Term k, KLabel visitLabel, KList visitList, KLabel ifLabel, KList ifList) {
    public static Term visit(Term k, Term visitLabelTerm, Term visitListTerm, Term ifLabelTerm, Term ifListTerm, TermContext context) {
        KLabel visitLabel = injectedKLabel(visitLabelTerm);
        KLabel ifLabel = injectedKLabel(ifLabelTerm);
        KList ifList = injectedKList(ifListTerm);
        KList visitList = injectedKList(visitListTerm);
        final ArrayList<Term> guardParams = new ArrayList<>();
        guardParams.add(k);
        guardParams.addAll(ifList.getContents());
        final ArrayList<Term> visitParams = new ArrayList<>();
        visitParams.add(k);
        visitParams.addAll(visitList.getContents());
        PrePostTransformer visitor = new BuiltinVisitor(context, ifLabel, guardParams, visitLabel, visitParams);
        return (Term) k.accept(visitor);
    }
}
