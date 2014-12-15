// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.*;


/**
 * Transformer class compiling strictness annotations into contexts.
 */
public class StrictnessToContexts extends CopyOnWriteTransformer {

    private static final String STRICT = "strict";
    private static final String SEQSTRICT = "seqstrict";
    private List<ModuleItem> items = new ArrayList<>();

    public StrictnessToContexts(Context context) {
        super("Strict Ops To Context", context);
    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
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
                throw KExceptionManager.compilerError(
                        "only productions of sort K, sort KLabel or of syntactic sorts can have "
                                + "strictness attributes",
                        this, prod);
            }

            if (prod.isSubsort()) {
                throw KExceptionManager.compilerError(
                        "Production is a subsort and cannot be strict.",
                        this, prod);
            }

            if (prod.isConstant() && !prod.getSort().equals(Sort.KLABEL)) {
                throw KExceptionManager.compilerError(
                        "Production is a constant and cannot be strict.",
                        this, prod);
            }

            final String strictType;
            if (!isSeq) {
                strictType = STRICT;
            } else {
                strictType = SEQSTRICT;
            }
            String attribute = prod.getAttribute(strictType);

            String[] strictAttrs = null;

            int arity = prod.getArityOfKItem();

            List<Integer> strictnessPositions = new ArrayList<>();
            if (attribute.isEmpty()) {
                for (int i = 1; i <= arity; i++) {
                    strictnessPositions.add(i);
                }
            } else {
                strictAttrs = attribute.split(",");
                for (String strictAttr : strictAttrs) {
                    try {
                        strictnessPositions.add(Integer.parseInt(strictAttr.trim()));
                    } catch (NumberFormatException e) {
                        throw KExceptionManager.compilerError(
                                "Expecting a number between 1 and " + arity + ", but found " + strictAttr + " as a" +
                                        " strict position in " + Arrays.toString(strictAttrs),
                                this, prod);
                    }
                }
            }

            for (int i = 0; i < strictnessPositions.size(); i++) {
                KApp app = (KApp) MetaK.getTerm(prod, context);
                KList list = (KList) app.getChild();
                if (context.kompileOptions.experimental.legacyKast) {
                    for (int j = 0; j < arity; ++j) {
                        list.getContents().get(j).setSort(Sort.KITEM);
                    }
                }

                // insert HOLE instead of the term
                list.getContents().set(-1 + strictnessPositions.get(i),
                        Hole.KITEM_HOLE);

                // is seqstrict the elements before the argument should be KResult
                if (isSeq) {
                    for (int j = 0; j < i; ++j) {
                        Term arg = list.getContents().get(-1 + strictnessPositions.get(j));
                        arg.setSort(Sort.KRESULT);
                    }
                }

                org.kframework.kil.Context ctx = new org.kframework.kil.Context();
                ctx.setBody(app);
                ctx.copyAttributesFrom(prod);
                ctx.setLocation(prod.getLocation());
                ctx.setSource(prod.getSource());
                ctx.addAttribute("cell", "k");
                items.add(ctx);
            }
        }

        return node;
    }

}

