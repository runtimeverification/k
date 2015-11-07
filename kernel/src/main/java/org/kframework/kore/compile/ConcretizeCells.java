// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.compile.ConfigurationInfo;
import org.kframework.compile.LabelInfo;
import org.kframework.definition.Module;
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
    final Module module;

    final AddParentCells addParentCells;
    final CloseCells closeCells;
    final SortCells sortCells;
    private final AddTopCellToRules addRootCell;

    public ConcretizeCells(ConfigurationInfo configurationInfo, LabelInfo labelInfo, SortInfo sortInfo, Module module, KExceptionManager kem) {
        this.configurationInfo = configurationInfo;
        this.labelInfo = labelInfo;
        this.sortInfo = sortInfo;
        this.module = module;
        addRootCell = new AddTopCellToRules(configurationInfo, labelInfo);
        addParentCells = new AddParentCells(configurationInfo, labelInfo);
        closeCells = new CloseCells(configurationInfo, sortInfo, labelInfo);
        sortCells = new SortCells(configurationInfo, labelInfo, module, kem);
    }

    public Sentence concretize(Sentence s) {
//        return sortCells.sortCells(
//                closeCells.close(
//                        addParentCells.concretize(
//                                addRootCell.addImplicitCells(s))));
        Sentence s1 = addRootCell.addImplicitCells(s);
        Sentence s2 = addParentCells.concretize(s1);
        Sentence s3 = closeCells.close(s2);

        Sentence s4 = sortCells.preprocess(s3);
        Sentence s5 = sortCells.sortCells(s4);
        Sentence s6 = sortCells.postprocess(s5);
        return s6;
    }
}
