// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import org.kframework.backend.unparser.KoreFilter;
import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.loader.Context;

/**
 * A visitor pattern which takes a StringBuilder which is used to construct a textual
 * representation of the term. Used with:
 * <pre>{@code
 * StringBuilder sb = new StringBuilder();
 * visitor.visitNode(node, sb);
 * String result = sb.toString();
 * }</pre>
 *
 * For an example implementation, see {@link KoreFilter}.
 * @author dwightguth
 *
 */
public class PrintVisitor extends AbstractVisitor<StringBuilder, Void, RuntimeException> {

    public PrintVisitor(Context context) {
        super(context);
    }

    public PrintVisitor(String name, Context context) {
        super(name, context);
    }

    @Override
    public Void defaultReturnValue(ASTNode node, StringBuilder _void) {
        return null;
    }

    @Override
    public <T extends ASTNode> T processChildTerm(T child, Void _void) {
        return child;
    }

    @Override
    public boolean visitChildren() {
        return true;
    }

    @Override
    public boolean cache() {
        return false;
    }

    @Override
    public <T extends ASTNode> boolean changed(T o, T n) {
        return false;
    }

    @Override
    public <T extends ASTNode> T copy(T original) {
        return original;
    }

}
