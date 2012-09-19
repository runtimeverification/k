package org.kframework.compile.sharing;

import java.util.HashSet;
import java.util.Set;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.kil.Cell;
import org.kframework.kil.Constant;
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.visitors.BasicVisitor;


/**
 * Collects klabels, sorts, and cell labels which are going to be declared
 * automatically.
 * 
 * @author andreiarusoaie
 * 
 */
public class SharedDataCollector extends BasicVisitor {

	Set<String> kLabels = new HashSet<String>();
	Set<String> sorts = new HashSet<String>();
	Set<String> cellLabels = new HashSet<String>()	;

	@Override
	public void visit(Constant node) {
		if (node.getSort().equals(Constants.KLABEL))
			kLabels.add(node.getValue());
		super.visit(node);
	}

	@Override
	public void visit(Cell cell) {
		cellLabels.add(cell.getLabel());
		super.visit(cell);
	}
	
	@Override
	public void visit(Sort node) {
		if (!MaudeHelper.basicSorts.contains(node.getName()))
			sorts.add(node.getName());
		super.visit(node);
	}
}
