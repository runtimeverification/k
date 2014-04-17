// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;


/**
 * Collects cell labels from visited modules.
 * @author andreiarusoaie
 */
public class CellLabelCollector extends BasicVisitor {
    public CellLabelCollector(Context context) {
        super(context);
    }

    public Set<String> cellLabels = new HashSet<String>()    ;

    // Skip every item other than configurations
    @Override
    public Void visit(Configuration c, Void _) {
        return super.visit(c, _);
    }
    @Override
    public Void visit(ModuleItem m, Void _) {     
        return null;   
    }
    
    @Override
    public Void visit(Cell cell, Void _) {
        cellLabels.add(cell.getLabel());
        return super.visit(cell, _);
    }    
}
