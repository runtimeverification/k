package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class MakeFreshVariables extends CopyOnWriteTransformer {

	private List<Variable> variables;

	public MakeFreshVariables(Context context, List<Variable> vars) {
		super("Replace a list of variables with symbolic values", context);
		this.variables = vars;
	}

	@Override
	public ASTNode transform(Variable node) throws TransformerException {
//		System.out.println("Var: " + node + " sort: " + node.getSort()
//				+ " is fresh " + node.isFresh());
		for (Variable v : variables) {
			if (v.getName().equals(node.getName()) && !node.isFresh()) {
//				System.out.println("Transformed: " + node + "(" + v.getSort()
//						+ ", " + node.isFresh() + ")");
				//return new AddSymbolicK(context).freshSymSortN(v.getSort(),
				//		RLBackend.idx);
				return KApp.of(KLabelConstant.of(AddSymbolicK.symbolicConstructor(v.getSort())), Token.kAppOf("#Id", v.getName()));
			}
		}
		return super.transform(node);
	}
}
