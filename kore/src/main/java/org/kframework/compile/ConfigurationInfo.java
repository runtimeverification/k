// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import scala.collection.immutable.Set;

import java.util.List;

/**
 * Information about the configuration structure used
 * in the configuration concretiziation passes.
 * Cells are identified by the sort containing the production
 * for the cell (this is more convenient when dealing also
 * with variables or functions of cell sort).
 */
public interface ConfigurationInfo {
    /** Number of proper ancestors of cell k */
    int getLevel(Sort k);

    /** Parent of cell k, or null */
    Sort getParent(Sort k);

    /** Children of cell k */
    List<Sort> getChildren(Sort k);

    /** Declared multiplicity of a cell */
    Multiplicity getMultiplicity(Sort k);

    /** True if sort k is actually a cell sort */
    boolean isCell(Sort k);

    /** True for cells which contain a term rather than other cells */
    boolean isLeafCell(Sort k);

    /** True for cells which contain other cells */
    boolean isParentCell(Sort k);

    Set<Sort> getCellBagSortsOfCell(Sort k);

    /** The declared sort of the contents of a leaf cell */
    Sort leafCellType(Sort k);

    /** The label for a cell */
    KLabel getCellLabel(Sort k);

    /** Returns a term which is the default cell of sort k,
     * probably an initializer macro */
    K getDefaultCell(Sort k);

    boolean isConstantInitializer(Sort k);

    /** Return the root cell of the configuration . */
    Sort getRootCell();
    /** Return the declared computation cell, by default the k cell */
    Sort getComputationCell();

    /** Returns the unit of a * or ? cell. */
    K getUnit(Sort k);

    /** Returns the concatenation operation of a multiplicity * cell. */
    KLabel getConcat(Sort k);

    /** Declared mulitplicitly of a cell */
    enum Multiplicity {
        /** Exactly one instance of this cell is required */
        ONE,
        /** This cell is optional but may not be repeated */
        OPTIONAL,
        /** This cell may occur any number of times, zero or more */
        STAR}
}
