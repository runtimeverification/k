package org.kframework.sharing;

import java.util.HashSet;
import java.util.Set;

import org.kframework.k.Cell;
import org.kframework.k.Constant;
import org.kframework.k.Sort;
import org.kframework.loader.Constants;
import org.kframework.transitions.maude.MaudeHelper;
import org.kframework.visitors.BasicVisitor;


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
