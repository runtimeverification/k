package ro.uaic.info.fmse.sharing;

import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;
import ro.uaic.info.fmse.visitors.BasicVisitor;

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
