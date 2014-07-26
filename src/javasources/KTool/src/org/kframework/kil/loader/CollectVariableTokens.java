// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.Visitor;

/**
 * Created with IntelliJ IDEA.
 * User: Andrei
 * Date: 14.11.2013
 * Time: 15:44
 * To change this template use File | Settings | File Templates.
 */
public class CollectVariableTokens extends BasicVisitor {
    public CollectVariableTokens(Context context) {
        super("Collect 'variable' tokens", context);
    }

    @Override
    public Void visit(Production node, Void _) {
        if  (node.containsAttribute("variable"))
            context.variableTokenSorts.add(node.getSort());
        return null;
    }
}
