package ro.uaic.info.fmse.transitions.maude;

import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;

public class KLabelsVisitor extends Visitor {

	@Override
	public void visit(ASTNode astNode) {
		if (astNode instanceof Constant) {
			Constant constant = (Constant) astNode;
			if (constant.getSort().equals(Constants.KLABEL))
				MaudeHelper.kLabels.add(constant.getValue());
		}
	}
}
