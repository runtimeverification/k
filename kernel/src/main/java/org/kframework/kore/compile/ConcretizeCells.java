// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KExceptionManager;

/**
 * Apply the entire configuration concretization process.
 * <p>
 * The input may freely use various configuration abstractions
 * and Full K flexibilites. See {@link IncompleteCellUtils} for a
 * description of the expected term structure.
 * The output will represent cells in
 * strict accordance with their declared fixed-arity productions.
 * <p>
 * This is a simple composition of the
 * {@link AddTopCellToRules}, {@link AddParentCells},
 * {@link CloseCells}, and {@link SortCells} passes,
 * see their documentation for details on the transformations.
 */
public class ConcretizeCells {
    final ConfigurationInfo configurationInfo;
    final LabelInfo labelInfo;
    final SortInfo sortInfo;

    final AddParentCells addParentCells;
    final CloseCells closeCells;
    final SortCells sortCells;
    private final AddTopCellToRules addRootCell;

    public ConcretizeCells(ConfigurationInfo configurationInfo, LabelInfo labelInfo, SortInfo sortInfo, KExceptionManager kem) {
        this.configurationInfo = configurationInfo;
        this.labelInfo = labelInfo;
        this.sortInfo = sortInfo;
        addRootCell = new AddTopCellToRules(configurationInfo, labelInfo);
        addParentCells = new AddParentCells(configurationInfo, labelInfo);
        closeCells = new CloseCells(configurationInfo, sortInfo, labelInfo);
        sortCells = new SortCells(configurationInfo, labelInfo, kem);
    }

    public Sentence concretize(Sentence s) {
        return sortCells.sortCells(
                closeCells.close(
                        addParentCells.concretize(
                                addRootCell.addImplicitCells(s))));
    }
}
