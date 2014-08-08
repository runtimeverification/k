// Copyright (c) 2012-2014 K Team. All Rights Reserved.

package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.general.GlobalSettings;

/**
 * Add the function attribute to rules which rewrite either a TermCons of
 * a production with a function or predicate attribute,
 * or a KApp of a KLabelConstant satisfying isPredicate
 * or corresponding to a production with a function or predicate attribute.
 */
public class ResolveFunctions extends CopyOnWriteTransformer {

    public ResolveFunctions(Context context) {
        super("Resolve Functions", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        Term body = node.getBody();
        if (body instanceof Rewrite) {
            body = ((Rewrite) body).getLeft();
        }
        if (body instanceof TermCons) {
            Production prod = ((TermCons) body).getProduction();
            if (prod.containsAttribute(Attribute.FUNCTION_KEY)
                    || prod.containsAttribute(Attribute.PREDICATE_KEY)) {
                node = addFunction(node);
            }
        }
        if (body instanceof KApp) {
            Term l = ((KApp) body).getLabel();
            if (l instanceof KLabelConstant) {
                KLabelConstant label = (KLabelConstant) l;
                if (label.isFunctional(context)) {
                    node = addFunction(node);
                }
            }
        }
        return node;
    }

    private Rule addFunction(Rule node) {
        node = node.shallowCopy();
        node.setAttributes(node.getAttributes().shallowCopy());
        if (node.containsAttribute("heat")) {
            GlobalSettings.kem.registerCompilerError(
                    "Top symbol tagged as function but evaluation strategies are not supported for functions.",
                    this, node);
        }
        node.putAttribute(Attribute.FUNCTION_KEY, "");
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }

}
