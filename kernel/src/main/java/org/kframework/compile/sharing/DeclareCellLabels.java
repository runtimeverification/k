// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.kil.Module;
import org.kframework.kil.Definition;
import org.kframework.kil.Sort;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.Context;

/**
 * Generate a sort CellLabel with a constant for each cell label in the configuration.
 * Must run after FlattenModules
 */
public class DeclareCellLabels extends BasicCompilerStep<Definition> {
    public DeclareCellLabels(Context context) {
        super(context);
    }

    @Override
    public String getName() {
        return "Generate CellLabel sort";
    }

    @Override
    public Definition compile(Definition def, String stepName) {
        Module module = def.getSingletonModule();

        CellLabelCollector labels = new CellLabelCollector(context);
        labels.visitNode(module);

        for (String cellLabel : labels.cellLabels) {
            module.addProduction(Sort.CELL_LABEL, new Terminal(cellLabel));
        }

        return def;
    }
}
