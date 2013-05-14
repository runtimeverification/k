package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class PriorityFilter extends BasicTransformer {
	public PriorityFilter(DefinitionHelper definitionHelper) {
		super("Priority filter", definitionHelper);
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		if (tc.getProduction(definitionHelper) == null)
			System.err.println(this.getClass() + ":" + " cons not found." + tc.getCons());
		if (tc.getProduction(definitionHelper).isListDecl()) {
			tc.getContents().set(0, (Term) tc.getContents().get(0).accept(new PriorityFilter2(tc, definitionHelper)));
			tc.getContents().set(1, (Term) tc.getContents().get(1).accept(new PriorityFilter2(tc, definitionHelper)));
		} else if (!tc.getProduction(definitionHelper).isConstant() && !tc.getProduction(definitionHelper).isSubsort()) {
			for (int i = 0, j = 0; i < tc.getProduction(definitionHelper).getItems().size(); i++) {
				if (tc.getProduction(definitionHelper).getItems().get(i).getType() == ProductionType.SORT) {
					// look for the outermost element
					if ((i == 0 || i == tc.getProduction(definitionHelper).getItems().size() - 1) && (tc.getContents().get(j) instanceof TermCons || tc.getContents().get(j) instanceof Ambiguity)) {
						tc.getContents().set(j, (Term) tc.getContents().get(j).accept(new PriorityFilter2(tc, definitionHelper)));
					}
					j++;
				}
			}
		}

		return super.transform(tc);
	}
}
