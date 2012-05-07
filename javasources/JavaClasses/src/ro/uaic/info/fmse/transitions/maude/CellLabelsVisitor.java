package ro.uaic.info.fmse.transitions.maude;

import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;

public class CellLabelsVisitor extends Visitor {

	public Set<String> cellLabels = new HashSet<String>();
	
	@Override
	public void visit(ASTNode astNode) {
		// I don't like this
		if (astNode instanceof Cell)
		{
			Cell cell = (Cell) astNode;
			cellLabels.add(cell.getLabel());
		}
	}

}
