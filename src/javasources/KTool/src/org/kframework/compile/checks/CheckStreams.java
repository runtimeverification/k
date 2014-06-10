// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.Cell;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.KSorts;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
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
            String sortName = node.getContents().getSort();
            if (!(context.isSubsortedEq("List", sortName) || context.dataStructureListSortOf(node.getContents().getSort()) != null)) {
                String msg = "Wrong sort in streaming cell. Expected List, but found " + node.getContents().getSort() + ".";
                GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), node.getFilename(), node.getLocation()));
            }
        }
        return null;
    }
}
