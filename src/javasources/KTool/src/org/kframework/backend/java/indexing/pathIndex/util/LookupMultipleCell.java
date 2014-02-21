package org.kframework.backend.java.indexing.pathIndex.util;

import org.apache.commons.collections15.MultiMap;
import org.apache.commons.collections15.multimap.MultiHashMap;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.symbolic.LocalVisitor;
import org.kframework.backend.java.symbolic.PrePostVisitor;

/**
 * @author OwolabiL
 */
public class LookupMultipleCell extends LocalVisitor {

    private LookupMultipleCell() {
        results = new MultiHashMap<>();
        cellsOfInterest = new String[]{"k", "in", "out"};
    }

    private final MultiMap<String, Cell> results;
    private final String[] cellsOfInterest;

    @Override
    public void visit(CellCollection cellCollection) {
        //TODO(OwolabiL): This is error prone. Check that it is really more efficient than a nested
        // loop.
        for (Cell cell : cellCollection.cells()) {
            if (cell.getLabel().equals(cellsOfInterest[0])) {
                results.put(cellsOfInterest[0], cell);
                continue;
            }

            if (cell.getLabel().equals(cellsOfInterest[1])) {
                results.put(cellsOfInterest[1], cell);
                continue;
            }

            if (cell.getLabel().equals(cellsOfInterest[2])) {
                results.put(cellsOfInterest[2], cell);
            }
        }
    }

    public static MultiMap<String, Cell> find(Term context) {
        LookupMultipleCell cellLocator = new LookupMultipleCell();
        PrePostVisitor recursiveCellFinder = new PrePostVisitor();
        recursiveCellFinder.getPreVisitor().addVisitor(cellLocator);
        context.accept(recursiveCellFinder);
        return cellLocator.results;
    }
}
