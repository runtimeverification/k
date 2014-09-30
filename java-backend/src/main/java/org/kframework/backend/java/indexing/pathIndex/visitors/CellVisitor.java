// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing.pathIndex.visitors;

import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.kil.loader.Context;

import java.util.ArrayList;
import java.util.List;

/**
 * This visitor class is used to traverse a term. It does the following in a single traversal:
 * (1) collect position strings from its kCell(s)
 * (2) selects i/o cells by name (this is a shortcoming of this approach as it specializes the
 * indexing technique to the, possibly user-defined cell names.)
 * Author: OwolabiL
 * Date: 2/26/14
 * Time: 12:56 PM
 *
 * @deprecated as of 04/16/2014 and will be replaced with a more general, faster algorithm in
 *              the future
 */
@Deprecated
class CellVisitor extends BottomUpVisitor {
    private final Context context;
    private Cell inCell;
    private Cell outCell;

    private final JavaExecutionOptions options;

    private List<String> kCellPStings = new ArrayList<>();

    CellVisitor(Context context, JavaExecutionOptions options) {
        this.context = context;
        this.options = options;
    }

    @Override
    public void visit(Cell cell) {
        if (cell.getLabel().equals(CellLabel.K)) {
            // get the pString from each k cell using a new visitor each time,
            // but accumulate the pStrings
            TermVisitor visitor = new TermVisitor(this.context, options, false);
            cell.getContent().accept(visitor);
            kCellPStings.addAll(visitor.getpStrings());
        } else if (cell.getLabel().equals(CellLabel.of("out"))) {
            outCell = cell;
        } else if (cell.getLabel().equals(CellLabel.of("in"))) {
            inCell = cell;
        } else if (cell.contentKind().isStructural()) {
            super.visit(cell);
        }
    }

    List<String> getkCellPStings() {
        return kCellPStings;
    }

    Cell getInCell() {
        return inCell;
    }

    Cell getOutCell() {
        return outCell;
    }
}
