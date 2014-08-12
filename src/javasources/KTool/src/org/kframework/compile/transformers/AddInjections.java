// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.KApp;
import org.kframework.kil.KItemProjection;
import org.kframework.kil.KLabelInjection;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
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

import com.google.common.collect.Lists;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


/**
 * @author AndreiS
 */
public class AddInjections extends CopyOnWriteTransformer{

    private enum TransformationState {
        NORMALIZE_PRODUCTIONS, TRANSFORM_PRODUCTIONS, TRANSFORM_TERMS, REMOVE_REDUNDANT_INJECTIONS
    }

    private TransformationState state;

    public AddInjections(Context context) {
        super("", context);
    }

    @Override
    public Module visit(Module module, Void _) {
        state = TransformationState.NORMALIZE_PRODUCTIONS;
        module = normalizeProductions(module);
        state = TransformationState.TRANSFORM_PRODUCTIONS;
        module = (Module) super.visit(module, _);
        state = TransformationState.TRANSFORM_TERMS;
        module = (Module) super.visit(module, _);
        state = TransformationState.REMOVE_REDUNDANT_INJECTIONS;
        module = (Module) super.visit(module, _);
        return module;
    }

    /* Phase one: transform productions such that each user-defined production has sort subsorted to KItem and each
     * not-terminal has sort subsorted to K */
    @Override
    public Syntax visit(Syntax node, Void _)  {
        if (state != TransformationState.TRANSFORM_PRODUCTIONS) {
            return node;
        }

        assert node.getPriorityBlocks().size() == 1;
        assert node.getPriorityBlocks().get(0).getProductions().size() == 1;

        Sort sort = node.getDeclaredSort().getSort();
        Production production = node.getPriorityBlocks().get(0).getProductions().get(0);
        production = (Production) visit(production, _);

        if ((sort.equals(Sort.KLABEL) && production.containsAttribute(Attribute.FUNCTION_KEY))
                || sort.equals(Sort.K) || sort.equals(Sort.KLIST)) {
            production = production.shallowCopy();
            production.setSort(Sort.KITEM);
        }

        if (sort.equals(Sort.BAG) && production.containsAttribute(Attribute.PATTERN_KEY)) {
            production = production.shallowCopy();
            production.setSort(Sort.MAP);
        }

        Syntax returnNode;
        if (production != node.getPriorityBlocks().get(0).getProductions().get(0)) {
            context.removeProduction(node.getPriorityBlocks().get(0).getProductions().get(0));
            context.addProduction(production);

            returnNode = node.shallowCopy();
            PriorityBlock priorityBlock = node.getPriorityBlocks().get(0).shallowCopy();
            returnNode.setPriorityBlocks(Collections.singletonList(priorityBlock));
            priorityBlock.setProductions(Collections.singletonList(production));

            if (!production.getSort().equals(sort)) {
                returnNode.setSort(returnNode.getDeclaredSort().shallowCopy());
                returnNode.getDeclaredSort().setSort(production.getSort());
            }
        } else {
            returnNode = node;
        }

        return returnNode;
    }

    /** Transforms {@code Sort} instances occurring as part of
     * {@link org.kframework.kil.ProductionItem}. Other instances are not changed. */
    @Override
    public NonTerminal visit(NonTerminal node, Void _) {
        assert state == TransformationState.TRANSFORM_PRODUCTIONS;

        if (needInjectionFrom(node.getSort())) {
            NonTerminal returnNode = node.shallowCopy();
            returnNode.setSort(Sort.KITEM);
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

        Sort sort = node.getProduction().getSort();
        if (needProjectionTo(sort)) {
            if (!node.getProduction().containsAttribute(Attribute.PATTERN_KEY)) {
                transformedNode.setSort(Sort.KITEM);
            } else {
                transformedNode.setSort(Sort.MAP);
            }
            // TODO (AndreiS): remove special case
            if (node.getProduction().getLabel().equals("#if_#then_#else_#fi") && !sort.equals(Sort.KLIST)) {
                return transformedNode;
            }
            return new KItemProjection(sort, transformedNode);
        } else {
            return transformedNode;
        }
    }

    /**
     * Private helper method that flattens productions of a given {@code Module}.
     *
     * @param module
     *            the module
     * @return the flattened module
     */
    private Module normalizeProductions(Module module) {
        module = module.shallowCopy();
        List<ModuleItem> newModuleItems = Lists.newArrayList();
        for (ModuleItem item : module.getItems()) {
            if (item instanceof Syntax) {
                Syntax syntax = (Syntax) item;
                for (PriorityBlock blk : syntax.getPriorityBlocks()) {
                    for (Production prod : blk.getProductions()) {
                        newModuleItems.add(
                            new Syntax(
                                syntax.getDeclaredSort(),
                                new PriorityBlock(blk.getAssoc(), prod)));
                    }
                }
            } else {
                newModuleItems.add(item);
            }
        }
        module.setItems(newModuleItems);
        return module;
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
    private boolean needInjectionFrom(Sort sort) {
        return sort.equals(Sort.KLABEL) || sort.equals(Sort.KLIST)
                || sort.equals(Sort.BAG) || sort.equals(Sort.BAG_ITEM)
                || sort.isCellSort();
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
    private boolean needProjectionTo(Sort sort) {
        return sort.equals(Sort.KLABEL) || sort.equals(Sort.KLIST)
                || sort.equals(Sort.K) || sort.equals(Sort.BAG)
                || sort.equals(Sort.BAG_ITEM) || sort.isCellSort();
    }

}
