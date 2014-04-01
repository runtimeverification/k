package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectBracketsVisitor extends BasicVisitor {

    public CollectBracketsVisitor(Context context) {
        super(context);
    }

    @Override
    public void visit(Production node) {
        if (node.isBracket()) {
            context.canonicalBracketForSort.put(node.getSort(), node);
        }
    }
}
