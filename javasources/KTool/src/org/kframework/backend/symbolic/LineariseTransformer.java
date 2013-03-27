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

/**
 * Replace each variable X in the left hand side with a new one Y
 * of the same sort and add the equality X == Y in the path condition.
 * @author andreiarusoaie
 *
 */
public class LineariseTransformer extends BasicTransformer {

	public LineariseTransformer() {
		super("Linearise Rules");
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (!node.containsAttribute(SymbolicBackend.SYMBOLIC) ) {
			return node;
		}

		
		if (node.getBody() instanceof Rewrite) {
			VariableReplaceTransformer vrt = new VariableReplaceTransformer(
					"");
			Rewrite rew = (Rewrite) node.getBody();
			rew.setLeft((Term) rew.getLeft().accept(vrt));
			
			Map<Variable, Variable> newGeneratedSV = vrt.getGeneratedVariables();
			Term condition = node.getCondition();

			List<Term> terms = new ArrayList<Term>();
			for (Entry<Variable, Variable> entry : newGeneratedSV.entrySet()) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(entry.getKey());
				vars.add(entry.getValue());

				String label = Constant.KEQ.getValue();
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

			node = node.shallowCopy();
			node.setBody(rew);
			node.setCondition(newCondition);
		}
		return node;
	}
}
