// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Definition;
import org.kframework.kil.KApp;
import org.kframework.kil.KItemProjection;
import org.kframework.kil.KLabelInjection;
import org.kframework.kil.KSorts;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


/**
 * @author AndreiS
 */
public class AddInjections extends CopyOnWriteTransformer{

    private enum TransformationState { TRANSFORM_PRODUCTIONS, TRANSFORM_TERMS, REMOVE_REDUNDANT_INJECTIONS }

    private TransformationState state;

//    private Stack<String> expectedSortStack;

    public AddInjections(Context context) {
        super("", context);
//        expectedSortStack = new Stack<>();
    }

    @Override
    public Definition visit(Definition definition, Void _)  {
        state = TransformationState.TRANSFORM_PRODUCTIONS;
        definition = (Definition) super.visit(definition, _);
        state = TransformationState.TRANSFORM_TERMS;
        definition = (Definition) super.visit(definition, _);
        state = TransformationState.REMOVE_REDUNDANT_INJECTIONS;
        definition = (Definition) super.visit(definition, _);
        return definition;
    }

    /* Phase one: transform productions such that each user-defined production has sort subsorted to KItem and each
     * not-terminal has sort subsorted to K */
    @Override
    public Syntax visit(Syntax node, Void _)  {
        if (state != TransformationState.TRANSFORM_PRODUCTIONS) {
            return node;
        }

        // TODO(AndreiS): normalize productions
        if (node.getPriorityBlocks().size() != 1 || node.getPriorityBlocks().get(0).getProductions().size() != 1) {
            return node;
        }

        assert node.getPriorityBlocks().size() == 1;
        assert node.getPriorityBlocks().get(0).getProductions().size() == 1;

        String sort = node.getSort().getName();
        Production production = node.getPriorityBlocks().get(0).getProductions().get(0);
        production = (Production) visit(production, _);

        if ((sort.equals(KSorts.KLABEL) && production.containsAttribute(Attribute.FUNCTION_KEY))
                || sort.equals(KSorts.K) || sort.equals(KSorts.KLIST)) {
            production = production.shallowCopy();
            production.setSort(KSorts.KITEM);
        }

        Syntax returnNode;
        if (production != node.getPriorityBlocks().get(0).getProductions().get(0)) {
            String cons = context.conses.inverse().get(
                    node.getPriorityBlocks().get(0).getProductions().get(0));
            context.conses.forcePut(cons, production);

            returnNode = node.shallowCopy();
            PriorityBlock priorityBlock = node.getPriorityBlocks().get(0).shallowCopy();
            returnNode.setPriorityBlocks(Collections.singletonList(priorityBlock));
            priorityBlock.setProductions(Collections.singletonList(production));

            if (!production.getSort().equals(sort)) {
                returnNode.setSort(returnNode.getSort().shallowCopy());
                returnNode.getSort().setName(production.getSort());
            }
        } else {
            returnNode = node;
        }

        return returnNode;
    }

    /** Transforms {@code Sort} instances occurring as part of
     * {@link org.kframework.kil.ProductionItem}. Other instances are not changed. */
    @Override
    public Sort visit(Sort node, Void _) {
        assert state == TransformationState.TRANSFORM_PRODUCTIONS;

        if (node.getName().equals(KSorts.KLABEL) || node.getName().equals(KSorts.KLIST)) {
            Sort returnNode = node.shallowCopy();
            returnNode.setName(KSorts.KITEM);
            return returnNode;
        } else {
            return node;
        }
    }


    /* Phase two: transform terms such that each term respects the transform productions */
    @Override
    public Rule visit(Rule node, Void _)  {
        // TODO(AndreiS): remove this check when include files do not contain the old List, Map, and Set
        if (node.containsAttribute("nojava")) {
            return node;
        }

        if (state != TransformationState.TRANSFORM_TERMS) {
            return node;
        }

        Rule transformedNode = (Rule) super.visit(node, _);
        if (!node.containsAttribute(Attribute.FUNCTION_KEY)) {
            return transformedNode;
        }

        assert transformedNode.getBody() instanceof Rewrite : "Deep rewrites are currently not allowed in function rules.";
        Term left = ((Rewrite) transformedNode.getBody()).getLeft();
        Term right = ((Rewrite) transformedNode.getBody()).getRight();
        if (!(left instanceof KItemProjection)) {
            return transformedNode;
        }

        transformedNode = transformedNode.shallowCopy();
        Rewrite transformedBody = (Rewrite) transformedNode.getBody().shallowCopy();
        transformedNode.setBody(transformedBody);
        transformedBody.setLeft(((KItemProjection) left).getTerm(), context);
        transformedBody.setRight(KApp.of(new KLabelInjection(right)), context);

        return transformedNode;
    }

    @Override
    public ASTNode visit(TermCons node, Void _)  {
        // TODO(AndreiS): find out why the assertion is failing
        // assert state == TransformationState.TRANSFORM_TERMS;
        if (state != TransformationState.TRANSFORM_TERMS) {
            return node;
        }

        boolean change = false;
        List<Term> transformedContents = new ArrayList<>();
        for (Term term : node.getContents()) {
            Term transformedTerm = (Term) this.visitNode(term);
            assert transformedTerm != null;

            if (needInjectionFrom(transformedTerm.getSort())) {
                transformedTerm = KApp.of(new KLabelInjection(transformedTerm));
            }
            transformedContents.add(transformedTerm);

            if (transformedTerm != term) {
                change = true;
            }
        }

        TermCons transformedNode;
        if (change) {
            transformedNode = node.shallowCopy();
            transformedNode.setContents(transformedContents);
        } else {
            transformedNode = node;
        }

        String sort = node.getProduction().getSort();
        if (needProjectionTo(sort)) {
            transformedNode.setSort(KSorts.KITEM);
            // TODO (AndreiS): remove special case
            if (node.getProduction().getLabel().equals("#if_#then_#else_#fi") && !sort.equals(KSorts.KLIST)) {
                return transformedNode;
            }
            return new KItemProjection(sort, transformedNode);
        } else {
            return transformedNode;
        }
    }

    /**
     * Private helper method that checks if an argument of a {@code TermCons}
     * with given sort needs to be injected to sort {@code KItem}.
     *
     * @param sort
     *            the declared sort of the argument
     * @return {@code true} if an injection is required; otherwise,
     *         {@code false}
     */
    private boolean needInjectionFrom(String sort) {
        return sort.equals(KSorts.KLABEL) || sort.equals(KSorts.KLIST)
                || sort.equals(KSorts.BAG) || sort.equals(KSorts.BAG_ITEM);
    }

    /**
     * Private helper method that checks if a function return value declared
     * with given sort needs a projection from sort {@code KItem} to its
     * declared sort.
     *
     * @param sort
     *            the declared sort of the function return value
     * @return {@code true} if a projection is required; otherwise,
     *         {@code false}
     */
    private boolean needProjectionTo(String sort) {
        return sort.equals(KSorts.KLABEL) || sort.equals(KSorts.KLIST)
                || sort.equals(KSorts.K) || sort.equals(KSorts.BAG)
                || sort.equals(KSorts.BAG_ITEM);
    }

}
