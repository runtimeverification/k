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

	public Set<String> cellLabels = new HashSet<String>()	;

	// Skip every item other than configurations
	@Override
	public void visit(Configuration c) {
		super.visit(c);
	}
	@Override
	public void visit(ModuleItem m) {		
	}
	
	@Override
	public void visit(Cell cell) {
		cellLabels.add(cell.getLabel());
		super.visit(cell);
	}	
}
