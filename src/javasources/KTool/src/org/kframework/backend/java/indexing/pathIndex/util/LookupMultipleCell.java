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
        for (Cell cell : cellCollection.cells()) {
            for (String aCellsOfInterest : cellsOfInterest) {
                if (cell.getLabel().equals(aCellsOfInterest)) {
                    results.put(aCellsOfInterest, cell);
                }
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
