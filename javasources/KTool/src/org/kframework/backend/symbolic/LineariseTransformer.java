package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class LineariseTransformer extends BasicTransformer {

	public LineariseTransformer() {
		super("Linearise Rules");
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (node.getBody() instanceof Rewrite) {

			VariableReplaceTransformer vrt = new VariableReplaceTransformer("");

			Rewrite rew = (Rewrite) node.getBody();
			rew.setLeft((Term) rew.getLeft().accept(vrt));
			
			Map<Variable, Variable> newVariables = vrt.getGeneratedVariables();

			Term condition = node.getCondition();

			List<Term> terms = new ArrayList<Term>();
			for (Entry<Variable, Variable> entry : newVariables.entrySet()) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(entry.getKey());
				vars.add(entry.getValue());
				String sort = entry.getValue().getSort().substring(1);
				String label = "'_==" + sort + "_";
				terms.add(new KApp(new Constant("KLabel", label), new KList(
						vars)));
			}

			if (terms.isEmpty())
				return node;

			Term newCondition = new KApp(Constant.ANDBOOL_KLABEL,
					new KList(terms));

			if (condition != null) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(condition);
				vars.add(newCondition);
				newCondition = new KApp(Constant.ANDBOOL_KLABEL,
						new KList(vars));
			}

			node.setBody(rew);
			node.setCondition(newCondition);
		}
		return node;
	}
}
