// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sentence;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KExceptionManager;

public class CheckListDecl extends BasicVisitor {

    public CheckListDecl(Context context) {
        super(context);
    }

    @Override
    public Void visit(Production node, Void _void) {
        if (node.isListDecl() && node.getSort().isBaseSort()) {
            String msg = node.getSort() + " can not be extended to be a list sort.";
            throw KExceptionManager.compilerError(msg, this, node);
        }

        if (node.isListDecl()) {
            UserList ul = (UserList) node.getItems().get(0);
            if (ul.getSort().equals(node.getSort())) {
                String msg = "Circular lists are not allowed.";
                throw KExceptionManager.compilerError(msg, this, node);
            }
        }

        for (int i = 0; i < node.getItems().size(); i++) {
            ProductionItem pi = node.getItems().get(i);
            if (pi instanceof UserList && node.getItems().size() > 1) {
                String msg = "Inline list declarations are not allowed.";
                throw KExceptionManager.compilerError(msg, this, pi);
            }
            // (radum) with the new parser lexical declarations are allowed in more places now.
            // so I removed the restriction for singleton lexical item per production.
        }
        return null;

    }

    @Override
    public Void visit(Sentence node, Void _void) {
        // optimization to not visit the entire tree
        return null;
    }
}
