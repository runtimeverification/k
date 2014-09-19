// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;


/**
 * Transformer class compiling strictness annotations into contexts.
 */
public class StrictnessToContexts extends CopyOnWriteTransformer {

    public static final String DEFAULT_STRICTNESS_CELL = "k";
    public static final String STRICT = "strict";
    public static final String SEQSTRICT = "seqstrict";
    private List<ModuleItem> items = new ArrayList<>();

    public StrictnessToContexts(Context context) {
        super("Strict Ops To Context", context);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        //collect the productions which have the attributes strict and seqstrict
        Set<Production> prods = SyntaxByTag.get(node, "strict", context);
        prods.addAll(SyntaxByTag.get(node, "seqstrict", context));
        if (prods.isEmpty()) {
            return node;
        }

        items = new ArrayList<>(node.getItems());
        node = node.shallowCopy();
        node.setItems(items);

        for (Production prod : prods) {
            assert prod.containsAttribute("strict") && !prod.containsAttribute("seqstrict")
                   || !prod.containsAttribute("strict") && prod.containsAttribute("seqstrict");
            Boolean isSeq = prod.containsAttribute("seqstrict");

            if (!(prod.getSort().isComputationSort() || prod.getSort().equals(Sort.KLABEL))) {
                GlobalSettings.kem.registerCompilerError(
                        "only productions of sort K, sort KLabel or of syntactic sorts can have "
                                + "strictness attributes",
                        this, prod);
                continue;
            }

            if (prod.isSubsort()) {
                GlobalSettings.kem.registerCompilerError(
                        "Production is a subsort and cannot be strict.",
                        this, prod);
                continue;
            }

            if (prod.isConstant() && !prod.getSort().equals(Sort.KLABEL)) {
                GlobalSettings.kem.registerCompilerError(
                        "Production is a constant and cannot be strict.",
                        this, prod);
                continue;
            }

            final String strictType;
            if (!isSeq) {
                strictType = STRICT;
            } else {
                strictType = SEQSTRICT;
            }
            String attribute = prod.getAttribute(strictType);
            String strictCell = DEFAULT_STRICTNESS_CELL;

            String[] strictAttrs = null;

            if (prod.getSort().equals(Sort.KLABEL)) {
                assert attribute.isEmpty() && strictCell.equals(DEFAULT_STRICTNESS_CELL) :
                        "Customized strictness for K labels not currently implemented";
                kLabelStrictness(prod, isSeq);
                continue;
            }

            List<Integer> strictnessPositions = new ArrayList<>();
            if (attribute.isEmpty()) {
                for (int i = 1; i <= prod.getArity(); i++) {
                    strictnessPositions.add(i);
                }
            } else {
                strictAttrs = attribute.split(",");
                for (String strictAttr : strictAttrs) {
                    try {
                        strictnessPositions.add(Integer.parseInt(strictAttr.trim()));
                    } catch (NumberFormatException e) {
                        GlobalSettings.kem.registerCompilerError(
                                "Expecting a number between 1 and " + prod.getArity() + ", but found " + strictAttr + " as a" +
                                        " strict position in " + strictAttrs,
                                this, prod);
                    }
                }
            }

            for (int i = 0; i < strictnessPositions.size(); i++) {
                TermCons termCons = (TermCons) MetaK.getTerm(prod, context);
                if (context.kompileOptions.experimental.legacyKast) {
                    for (int j = 0; j < prod.getArity(); ++j) {
                        termCons.getContents().get(j).setSort(Sort.KITEM);
                    }
                }

                // insert HOLE instead of the term
                termCons.getContents().set(-1 + strictnessPositions.get(i),
                        Hole.KITEM_HOLE);

                // is seqstrict the elements before the argument should be KResult
                if (isSeq) {
                    for (int j = 0; j < i; ++j) {
                        Term arg = termCons.getContents().get(-1 + strictnessPositions.get(j));
                        arg.setSort(Sort.KRESULT);
                    }
                }

                org.kframework.kil.Context ctx = new org.kframework.kil.Context();
                ctx.setBody(termCons);
                ctx.copyAttributesFrom(prod);
                ctx.setLocation(prod.getLocation());
                ctx.setSource(prod.getSource());
                ctx.addAttribute("cell", "k");
                items.add(ctx);
            }
        }

        return node;
    }

    /* Add context KLabel(KList1 ,, HOLE ,, KList2).
     * If KLabel is seqstrict then add the condition isKResult(KList1)
     */
    private void kLabelStrictness(Production prod, boolean isSeq) {
        List<Term> contents = new ArrayList<>(3);
        //first argument is a variable of sort KList
        Variable variable = Variable.getFreshVar(Sort.KLIST);
        contents.add(variable);
        //second is a HOLE
        contents.add(Hole.KITEM_HOLE);
        //third argument is a variable of sort KList
        contents.add(Variable.getFreshVar(Sort.KLIST));
        KApp kapp = new KApp(MetaK.getTerm(prod, context), new KList(contents));
        //make a context from the TermCons
        org.kframework.kil.Context ctx = new org.kframework.kil.Context();
        ctx.setBody(kapp);
        ctx.copyAttributesFrom(prod);
        ctx.setLocation(prod.getLocation());
        ctx.setSource(prod.getSource());
        if (isSeq) {
            //set the condition
            KApp condApp = KApp.of(KLabelConstant.KRESULT_PREDICATE, variable);
            ctx.setRequires(condApp);
            ctx.removeAttribute("seqstrict");
        } else {
            ctx.removeAttribute("strict");
        }
        //add the context
        items.add(ctx);
    }

}

