package ro.uaic.info.fmse.transitions.maude;

import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.parsing.BasicVisitor;

public class CellLabelsVisitor extends BasicVisitor {

	public Set<String> cellLabels = new HashSet<String>();

	@Override
	public void visit(Cell cell) {
		cellLabels.add(cell.getLabel());
		super.visit(cell);
	}
}
