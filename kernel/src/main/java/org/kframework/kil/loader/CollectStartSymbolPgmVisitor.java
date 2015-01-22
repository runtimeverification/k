// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;

/**
 * Collect the $PGM sort from the final configuration it encounters
 *
 * @author Radu
 *
 */
public class CollectStartSymbolPgmVisitor extends BasicVisitor {

    public CollectStartSymbolPgmVisitor(Context context) {
        super(context);
    }

    @Override
    public Void visit(Rule node, Void _void) {
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Syntax node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Variable node, Void _void) {
        assert node.getName().startsWith("$") : "Configuration variables must start with $ symbol.";
        context.configVarSorts.put(node.getName().substring(1), node.getSort());
        return null;
    }
}
