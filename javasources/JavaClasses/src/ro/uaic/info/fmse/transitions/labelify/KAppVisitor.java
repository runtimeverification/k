package ro.uaic.info.fmse.transitions.labelify;

import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;

public class KAppVisitor extends Visitor {

	public Term cellLabels;

	@Override
	public void visit(ASTNode astNode) {
		// I don't like this
		/*if (astNode instanceof Cell) {
			Cell cell = (Cell) astNode;
			cellLabels.add(cell.getLabel());
		}*/
	}

}


/*

f(5)

'f(# 5(.List{K}))

env(X |-> 5)
'env(Map2KLabel(C |-> 5)(.List{K}))
*/