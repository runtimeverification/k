// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.Lexical;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

public class CheckListDecl extends BasicVisitor {

    public CheckListDecl(Context context) {
        super(context);
    }

    @Override
    public Void visit(Production node, Void _) {
        if (node.isListDecl() && Sort.isBasesort(node.getSort())) {
            String msg = node.getSort() + " can not be extended to be a list sort.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }

        if (node.isListDecl()) {
            UserList ul = (UserList) node.getItems().get(0);
            if (ul.getSort().equals(node.getSort())) {
                String msg = "Circular lists are not allowed.";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
            }
        }

        for (int i = 0; i < node.getItems().size(); i++) {
            ProductionItem pi = node.getItems().get(i);
            if (pi instanceof UserList && node.getItems().size() > 1) {
                String msg = "Inline list declarations are not allowed.";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), pi.getFilename(), pi.getLocation()));
            }
            if (pi instanceof Lexical && node.getItems().size() > 1) {
                String msg = "Inline lexical/token declarations are not allowed.";
                GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), pi.getFilename(), pi.getLocation()));
            }
        }
        return null;

    }

    @Override
    public Void visit(Sentence node, Void _) {
        // optimization to not visit the entire tree
        return null;
    }
}
