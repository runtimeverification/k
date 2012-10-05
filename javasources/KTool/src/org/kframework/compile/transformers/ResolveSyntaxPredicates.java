package org.kframework.compile.transformers;


import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.ListOfK;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ResolveSyntaxPredicates extends CopyOnWriteTransformer {
	
	
	
	public ResolveSyntaxPredicates() {
		super("Resolve syntax predicates");
	}
	
	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		boolean change = false;
		Set<Variable> vars = MetaK.getVariables(node.getBody());
		ListOfK ands = new ListOfK();
		Term condition = node.getCondition();
		if (null != condition) {
			ands.getContents().add(condition);
		}
		for (Variable var : vars) {
//			if (!var.isUserTyped()) continue;
			if (MetaK.isKSort(var.getSort())) continue;
			change = true;
			ands.getContents().add(getPredicateTerm(var));
		}
		if (!change) return node;
		if (ands.getContents().size() > 1) {
			condition = new KApp(new Constant("KLabel", "'#andBool"), ands);
		} else {
			condition = ands.getContents().get(0);
		}
		node = node.shallowCopy();
		node.setCondition(condition);
		return node;
	}

	private Term getPredicateTerm(Variable var) {
		return new KApp(new Constant("KLabel", "is" + var.getSort()), var);
	}

}
