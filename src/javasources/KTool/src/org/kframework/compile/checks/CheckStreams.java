// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.Cell;
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.general.GlobalSettings;

public class CheckStreams extends BasicVisitor {

    public CheckStreams(Context context) {
        super("Check Streaming Cell Contents", context);
    }

    @Override
    public Void visit(Cell node, Void _) {

        this.visitNode(node.getContents());
        String stream = node.getCellAttributes().get("stream");
        if (stream != null) {
            Sort sort = node.getContents().getSort();
            if (!(context.isSubsortedEq(Sort.LIST, sort) || context.dataStructureListSortOf(node.getContents().getSort()) != null)) {
                String msg = "Wrong sort in streaming cell. Expected List, but found " + node.getContents().getSort() + ".";
                GlobalSettings.kem.registerCriticalError(msg, this, node);
            }
        }
        return null;
    }
}
