// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.KilProperty;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.*;
import java.util.List;
import java.util.Set;

/**
 * Transformer replacing concrete syntax declarations by KLabel declarations.
 */
@KilProperty.Ensures({KilProperty.NO_CONCRETE_SYNTAX, KilProperty.NO_CONCRETE_SYNTAX_DECLARATIONS})
public class FlattenSyntax extends CopyOnWriteTransformer {
    Set<String> listUnits = new HashSet<>();
    boolean isComputation = false;

    public FlattenSyntax(Context context) {
        super("Syntax K to Abstract K", context);
    }

    @Override
    public ASTNode visit(Definition node, Void _void)  {
        node = (Definition) new FlattenTerms(context).visitNode(node);
        //TODO:  Remove the above once we figure out how to split the two phases
        return super.visit(node, _void);
    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
        listUnits.clear();
        node = (Module) super.visit(node, _void);
        if (listUnits.isEmpty())
            return node;

        for (String listUnit : listUnits) {
            node.addConstant(Sort.KLABEL, listUnit);
        }
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _void)  {
        if (!node.getDeclaredSort().getSort().isComputationSort()) {
            isComputation = false;
            return super.visit(node, _void);
        }
        isComputation = true;
        node = (Syntax) super.visit(node, _void);
        node.setSort(new NonTerminal(Sort.KLABEL));
        return node;
    }

    @Override
    public ASTNode visit(Production node, Void _void)  {
        if (node.containsAttribute("KLabelWrapper"))
            return node;
        if (!isComputation)
            return super.visit(node, _void);
        if (node.isSubsort())
            return null;
        String arity = String.valueOf(node.getArity());
        Attributes attrs = node.getAttributes().shallowCopy();
        if (node.isListDecl()) {
            listUnits.add(node.getTerminatorKLabel());
        }
        node = node.shallowCopy();
        List<ProductionItem> pis = new ArrayList<>();
        pis.add(new Terminal(node.getKLabel()));
        node.setItems(pis);
        attrs.add(Attribute.of("arity", arity));
        node.setAttributes(attrs);
        node.setSort(Sort.KLABEL);
        return node;
    }

    @Override
    public ASTNode visit(NonTerminal node, Void _void)  {
        if (!node.getSort().isComputationSort())
            return node;
        return new NonTerminal(Sort.K);
    }
}
