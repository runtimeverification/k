// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.parser.outer.Outer;
import org.kframework.parser.outer.ParseException;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;


/**
 * Transformer class compiling strictness annotations into contexts.
 */
public class StrictnessToContexts extends CopyOnWriteTransformer {

    public static final String ALL = "all";
    public static final String OTHER = "other";
    public static final String DEFAULT_STRICTNESS_CELL = "k";
    public static final String STRICT = "strict";
    public static final String SEQSTRICT = "seqstrict";
    public static final String CONTEXT = "context";
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
                if (prod.getKLabel() == null) {
                    GlobalSettings.kem.registerCompilerError(
                            "Production is a subsort and cannot be strict.",
                            this, prod);
                    continue;
                } else {
                    Attributes attributes = prod.getAttributes();
                    prod = new Production(new NonTerminal(Sort.KLABEL),
                            Collections.<ProductionItem>singletonList(new Terminal(prod.getKLabel())));
                    prod.setAttributes(attributes);
                    kLabelStrictness(prod, isSeq);
                    continue;
                }
            }

            if (prod.isConstant() && !prod.getSort().equals(Sort.KLABEL)) {
                GlobalSettings.kem.registerCompilerError(
                        "Production is a constant and cannot be strict.",
                        this, prod);
                continue;
            }

            final String strictType;
            Attribute allStrictAttr;
            if (!isSeq) {
                strictType = STRICT;
                allStrictAttr = prod.getAttributes().get(strictType);
            } else {
                strictType = SEQSTRICT;
                allStrictAttr = prod.getAttributes().get(strictType);
            }
            String attribute = allStrictAttr.getValue();
            String allStrictAttrKey = allStrictAttr.getKey();
            String strictCell;
            if (allStrictAttrKey.length() == strictType.length()) {
                strictCell = DEFAULT_STRICTNESS_CELL;
            } else {
                if (allStrictAttrKey.charAt(strictType.length()) != '<' ||
                        allStrictAttrKey.charAt(allStrictAttrKey.length()-1) != '>') {
                    GlobalSettings.kem.registerCompilerError(
                            "Expecting attribute " + strictType + "<cell>, but got " + allStrictAttrKey,
                            this, prod);
                }
                strictCell = allStrictAttrKey.substring(1 + strictType.length(), allStrictAttrKey.length() - 1);
            }
            Attribute strictCellAttr = new Attribute(Attribute.CELL_KEY, strictCell);

            Attributes strictAttrs = null;
            if (attribute.isEmpty()) {
                attribute = ALL;
            }

            if (prod.getSort().equals(Sort.KLABEL)) {
                assert attribute.equals(ALL) && strictCell.equals(DEFAULT_STRICTNESS_CELL) :
                        "Customized strictness for K labels not currently implemented";
                kLabelStrictness(prod, isSeq);
                continue;
            }

            try {
                strictAttrs = Outer.parseAttributes(attribute, prod.getSource());
            } catch (ParseException e) {
                GlobalSettings.kem.registerCompilerError(
                        "Strictness attributes " + attribute + " could not be parsed." +
                                "Parse error: " + e.getMessage(),
                        this, e, prod);
            }
            for (Attribute strictAttr : strictAttrs.values()) {
                Attributes strictAttrAttrs = null;
                String strictAttrValue = strictAttr.getValue();
                if (strictAttrValue.isEmpty()) strictAttrAttrs = new Attributes();
                else {
                    try {
                        strictAttrAttrs = Outer.parseAttributes(strictAttrValue, prod.getSource());
                    } catch (ParseException e) {
                        GlobalSettings.kem.registerCompilerError(
                                "Strictness attributes could not be parsed for " + strictAttrValue + "." +
                                        "Parse error: " + e.getMessage(),
                                this, e, prod);
                    }
                }
                strictAttr.setAttributes(strictAttrAttrs);
            }
            List<Attribute> newStrictAttrs = new ArrayList<>();
            java.util.Map<Integer,Integer> strictPositions = new HashMap<>();
            for (Attribute strictAttr : strictAttrs.values()) {
                boolean other = false;
                String strictAttrKey = strictAttr.getKey();
                String strictAttrValue = strictAttr.getValue();
                if (strictAttrKey.equals(ALL)) {
                    for (Attribute newStrictAttr :  newStrictAttrs) {
                        newStrictAttr.getAttributes().putAll(strictAttr.getAttributes());
                        newStrictAttr.setSource(strictAttr.getSource());
                        newStrictAttr.setLocation(strictAttr.getLocation());
                    }
                    other = true;
                } else if (strictAttrKey.equals(OTHER)) {
                    other = true;
                } else {
                    int i = 0;
                    try {
                        i = Integer.parseInt(strictAttrKey);
                    } catch (NumberFormatException e) {
                        GlobalSettings.kem.registerCompilerError(
                                "Expecting " + ALL + ", " + OTHER + ", or a number, but found " + strictAttrKey + " as a" +
                                        " strict position in " + strictAttrValue,
                                this, e, prod);
                    }
                    if (i <= 0 || i > prod.getArity()) {
                        GlobalSettings.kem.registerCompilerError(
                                "Expecting a number between 1 and " + prod.getArity() + ", but found " + strictAttrKey + " as a" +
                                        " strict position in " + strictAttrValue,
                                this, prod);
                    }
                    if (!strictPositions.containsKey(i)) {
                        strictPositions.put(i, newStrictAttrs.size());
                        Attribute newStrictAttr = strictAttr.shallowCopy();
                        newStrictAttr.setAttributes(new Attributes());
                        newStrictAttr.getAttributes().add(strictCellAttr);
                        newStrictAttr.getAttributes().putAll(strictAttr.getAttributes());
                        newStrictAttr.setSource(strictAttr.getSource());
                        newStrictAttr.setLocation(strictAttr.getLocation());
                        newStrictAttrs.add(strictAttr);
                    } else {
                        newStrictAttrs.get(strictPositions.get(i)).getAttributes().putAll(strictAttr.getAttributes());
                        newStrictAttrs.get(strictPositions.get(i)).setSource(strictAttr.getSource());
                        newStrictAttrs.get(strictPositions.get(i)).setLocation(strictAttr.getLocation());
                    }
                }
                if (other) {
                    for (int i = 1; i <= prod.getArity(); ++i) {
                        if (!strictPositions.containsKey(i)) {
                            strictPositions.put(i,newStrictAttrs.size());
                            Attribute newStrictAttr = new Attribute(Integer.toString(i), strictAttrValue);
                            newStrictAttr.setAttributes(new Attributes());
                            newStrictAttr.getAttributes().add(strictCellAttr);
                            newStrictAttr.getAttributes().putAll(strictAttr.getAttributes());
                            newStrictAttr.setSource(strictAttr.getSource());
                            newStrictAttr.setLocation(strictAttr.getLocation());
                            newStrictAttrs.add(newStrictAttr);
                        }
                    }
                }
            }

            for (int i = 0; i < newStrictAttrs.size(); i++) {
                Attribute newStrictAttr = newStrictAttrs.get(i);
                TermCons termCons = (TermCons) MetaK.getTerm(prod, context);

                // insert HOLE instead of the term
                termCons.getContents().set(-1 + Integer.parseInt(newStrictAttr.getKey()),
                        getHoleTerm(newStrictAttr.getAttributes(), prod));

                // is seqstrict the elements before the argument should be KResult
                KApp sideCond = null;
                if (isSeq) {
                    for (int j = 0; j < i; ++j) {
                        Term arg = termCons.getContents().get(-1 + Integer.parseInt(newStrictAttrs.get(j).getKey()));
                        arg.setSort(Sort.KRESULT);
                    }
                }

                org.kframework.kil.Context ctx = new org.kframework.kil.Context();
                ctx.setBody(termCons);
                ctx.setAttributes(new Attributes());
                ctx.getAttributes().putAll(prod.getAttributes());
                ctx.setLocation(prod.getLocation());
                ctx.setSource(prod.getSource());
                String strictContext = newStrictAttr.getAttribute(CONTEXT);
                if (strictContext != null) {
                    Set<Production> productions = getStrictContextProductions(strictContext, prod);
                    assert productions.size()==1 : "Expecting only one production for context " +
                            strictContext + " but found " + productions.size() + ": " + productions;
                    Production strictContextProd = productions.iterator().next();
                    String strictContextProdAttribute = strictContextProd.getAttribute(CONTEXT);
                    if (!strictContextProdAttribute.isEmpty()) {
                        try {
                            Attributes strictContextAttrs = Outer.parseAttributes(
                                    strictContextProdAttribute, strictContextProd.getSource());
                            ctx.getAttributes().putAll(strictContextAttrs);
                        } catch (ParseException e) {
                            GlobalSettings.kem.registerCompilerError(
                                "Context attributes could not be parsed for " + strictContextProdAttribute + ".\n" +
                                        "Parse error: " + e.getMessage(),
                                this, e, strictContextProd);
                        }
                    }
                }
                ctx.getAttributes().putAll(newStrictAttr.getAttributes());
                if (sideCond != null)
                    ctx.setRequires(sideCond);
                items.add(ctx);
            }
        }

        return node;
    }

    private Term getHoleTerm(Attributes strictnessAttributes, Production prod) {
        Term hole;
        Attribute strictType = null;
        if (strictnessAttributes != null) {
            strictType = strictnessAttributes.get(CONTEXT);
        }
        if (null == strictType) {
            hole = Hole.KITEM_HOLE;
        } else {
            getStrictContextProductions(strictType.getValue(), prod);
            hole = new Rewrite(Hole.KITEM_HOLE, KApp.of(KLabelConstant.of(strictType.getValue()), Hole.KITEM_HOLE),context);
        }
        return hole;
    }

    private Set<Production> getStrictContextProductions(String strictType, Production prod) {
        Set<Production> productions = context.klabels.get(strictType);
        if (productions == null) {
            GlobalSettings.kem.registerCompilerError(
                        "Strictness context label " + strictType + " does not correspond to any production.",
                        this, prod);
        }
        return productions;
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
        contents.add(getHoleTerm(null, prod));
        //third argument is a variable of sort KList
        contents.add(Variable.getFreshVar(Sort.KLIST));
        KApp kapp = new KApp(MetaK.getTerm(prod, context), new KList(contents));
        //make a context from the TermCons
        org.kframework.kil.Context ctx = new org.kframework.kil.Context();
        ctx.setBody(kapp);
        ctx.setAttributes(prod.getAttributes());
        ctx.setLocation(prod.getLocation());
        ctx.setSource(prod.getSource());
        if (isSeq) {
            //set the condition
            KApp condApp = KApp.of(KLabelConstant.KRESULT_PREDICATE, variable);
            ctx.setRequires(condApp);
            ctx.getAttributes().remove("seqstrict");
        } else {
            ctx.getAttributes().remove("strict");
        }
        //add the context
        items.add(ctx);
    }

}

