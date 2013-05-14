package org.kframework.compile.transformers;


import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Set;

public class ResolveSyntaxPredicates extends CopyOnWriteTransformer {
	
	
	
	public ResolveSyntaxPredicates(DefinitionHelper definitionHelper) {
		super("Resolve syntax predicates", definitionHelper);
	}
	
	
	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		boolean change = false;
		Set<Variable> vars = MetaK.getVariables(node.getBody(), definitionHelper);
		KList ands = new KList();
		Term condition = node.getCondition();
		if (null != condition) {
			ands.getContents().add(condition);
		}
		for (Variable var : vars) {
//			if (!var.isUserTyped()) continue;
			if (MetaK.isKSort(var.getSort(definitionHelper))) continue;
			change = true;
			ands.getContents().add(getPredicateTerm(var));
		}
		if (!change) return node;
		if (ands.getContents().size() > 1) {
			condition = new KApp(KLabelConstant.ANDBOOL_KLABEL, ands);
		} else {
			condition = ands.getContents().get(0);
		}
		node = node.shallowCopy();
		node.setCondition(condition);
		return node;
	}

	private Term getPredicateTerm(Variable var) {
		return KApp.of(definitionHelper, KLabelConstant.of(AddPredicates.predicate(var.getSort(definitionHelper)), definitionHelper), var);
	}

}
