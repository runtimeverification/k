package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSorts;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;


/**
 * Transformer class compiling strictness annotations into contexts.
 */
public class StrictnessToContexts extends CopyOnWriteTransformer {

    private List<ModuleItem> items = new ArrayList<ModuleItem>();

    public StrictnessToContexts(Context context) {
        super("Strict Ops To Context", context);
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        //collect the productions which have the attributes strict and seqstrict
        Set<Production> prods = SyntaxByTag.get(node, "strict", context);
        prods.addAll(SyntaxByTag.get(node, "seqstrict", context));
        if (prods.isEmpty()) {
            return node;
        }

        items = new ArrayList<ModuleItem>(node.getItems());
        node = node.shallowCopy();
        node.setItems(items);

        for (Production prod : prods) {
            assert prod.containsAttribute("strict") && !prod.containsAttribute("seqstrict")
                   || !prod.containsAttribute("strict") && prod.containsAttribute("seqstrict");
            Boolean isSeq = prod.containsAttribute("seqstrict");

            if (!MetaK.isComputationSort(prod.getSort()) || prod.getSort().equals(KSorts.KLABEL)) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.COMPILER,
                        "only productions of sort K, sort KLabel or of syntactic sorts can have "
                        + "strictness attributes",
                        getName(),
                        prod.getFilename(),
                        prod.getLocation()));
                continue;
            }

            if (prod.isSubsort()) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.COMPILER,
                        "Production is a subsort and cannot be strict.",
                        getName(),
                        prod.getFilename(),
                        prod.getLocation()));
                continue;
            }

            if (prod.isConstant()) {
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                        KExceptionGroup.COMPILER,
                        "Production is a constant and cannot be strict.",
                        getName(),
                        prod.getFilename(),
                        prod.getLocation()));
                continue;
            }

            if (prod.getSort().equals(KSorts.KLABEL)) {
                kLabelStrictness(prod, isSeq);
                continue;
            }

            String attribute;
            if (!isSeq) {
                attribute = prod.getAttribute("strict");
            } else {
                attribute = prod.getAttribute("seqstrict");
            }

            ArrayList<Integer> arguments = new ArrayList<Integer>();
            if (!attribute.isEmpty()) {
                for (String s : attribute.split(",")) {
                    try {
                        int i = Integer.parseInt(s.trim());
                        if (i <= 0 || i > prod.getArity()) {
                            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                                    KExceptionGroup.COMPILER,
                                    "strictness argument '" + i + "'out of bounds: ",
                                    getName(),
                                    prod.getFilename(),
                                    prod.getLocation()));
                            continue;
                        }
                        arguments.add(i - 1);
                    } catch (NumberFormatException e) {
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                                KExceptionGroup.COMPILER,
                                "unexpected strictness argument '" + s + "'; expected integer",
                                getName(),
                                prod.getFilename(),
                                prod.getLocation()));
                    }
                }
            } else {
                for (int i = 0; i < prod.getArity(); ++i) {
                    arguments.add(i);
                }
            }

            for (int i = 0; i < arguments.size(); ++i) {
                TermCons termCons = (TermCons) MetaK.getTerm(prod, context);
                for (int j = 0; j < prod.getArity(); ++j) {
                    if (GlobalSettings.matchingLogic) {
                        /* the Java Rewrite Engine only supports strictness with KItem variables */
                        termCons.getContents().get(j).setSort(KSorts.KITEM);
                    } else {
                        termCons.getContents().get(j).setSort(KSorts.K);
                    }
                }

                // insert HOLE instead of the term
                termCons.getContents().set(arguments.get(i), Hole.KITEM_HOLE);

                // is seqstrict the elements before the argument should be KResult
                if (isSeq) {
                    for (int j = 0; j < i; ++j) {
                        termCons.getContents().get(arguments.get(j)).setSort(KSorts.KRESULT);
                    }
                }

                org.kframework.kil.Context ctx = new org.kframework.kil.Context();
                ctx.setBody(termCons);
                ctx.setAttributes(prod.getAttributes());
                items.add(ctx);
            }
        }

        return node;
    }

    /* Add context KLabel(KList1 ,, HOLE ,, KList2).
     * If KLabel is seqstrict then add the condition isKResult(KList1)
     */
    private void kLabelStrictness(Production prod, boolean isSeq) {
        List<Term> contents = new ArrayList<Term>(3);
        //first argument is a variable of sort KList
        Variable variable = Variable.getFreshVar(KSorts.KLIST);
        contents.add(variable);
        //second is a HOLE
        contents.add(Hole.KITEM_HOLE);
        //third argument is a variable of sort KList
        contents.add(Variable.getFreshVar(KSorts.KLIST));
        KApp kapp = new KApp(MetaK.getTerm(prod, context), new KList(contents));
        //make a context from the TermCons
        org.kframework.kil.Context ctx = new org.kframework.kil.Context();
        ctx.setBody(kapp);
        ctx.setAttributes(prod.getAttributes());
        if (isSeq) {
            //set the condition
            KApp condApp = KApp.of(KLabelConstant.KRESULT_PREDICATE, variable);
            ctx.setCondition(condApp);
            ctx.getAttributes().remove("seqstrict");
        } else {
            ctx.getAttributes().remove("strict");
        }
        //add the context
        items.add(ctx);
    }

}

