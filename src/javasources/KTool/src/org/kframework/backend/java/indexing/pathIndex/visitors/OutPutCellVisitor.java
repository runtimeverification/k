// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.symbolic.BottomUpVisitor;

/**
 * This visitor traverses the output cell and checks whether the "buffer" is empty.
 * <p/>
 * Author: OwolabiL
 * Date: 2/26/14
 * Time: 1:41 PM
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
class OutPutCellVisitor extends BottomUpVisitor {
    public static final String BUFFER_LABEL = "'#buffer";

    public boolean isAddOutCell() {
        return addOutCell;
    }

    private boolean addOutCell;

    OutPutCellVisitor() {
        addOutCell = false;
    }

    @Override
    public void visit(BuiltinList node) {
        for (Term content : node.elements()) {
            content.accept(this);
        }
    }

    @Override
    public void visit(KItem kItem) {
        if (kItem.kLabel().toString().equals(BUFFER_LABEL)) {
            Term bufferTerm = ((KList) kItem.kList()).get(0);
            if (bufferTerm instanceof Token && !((Token) bufferTerm).value().equals("\"\"")) {
                addOutCell = true;
            }
        }
    }
}
