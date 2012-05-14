package ro.uaic.info.fmse.lists;

import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.Terminal;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;

public class EmptyListsVisitor extends Visitor {

	@Override
	public ASTNode visit(ASTNode astNode) {

		// traverse
		astNode.all(this);

		if (astNode instanceof TermCons) {
			TermCons tc = (TermCons) astNode;
			Production production = DefinitionHelper.conses.get("\"" + tc.getCons() + "\"");

			int i = 0, j = 0;
			while (i < production.getItems().size() && j < tc.getContents().size()) {
				if (production.getItems().get(i) instanceof Terminal)
					i++;
				else if (production.getItems().get(i) instanceof Sort)
					// if the sort of the j-th term is a list sort
					if (isListSort(((Sort) production.getItems().get(i)).toString()) && !isListSort(tc.getContents().get(j).getSort())) {
						tc.getContents().add(new Empty("generated", "generated", ((Sort) production.getItems().get(i)).toString()));
					}
			}
		}

		return astNode;
	}

	public static boolean isListSort(String sort) {
		return DefinitionHelper.listSeparators.containsKey(sort);
	}
}
