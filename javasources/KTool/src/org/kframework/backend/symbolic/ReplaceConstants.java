package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KList;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class ReplaceConstants extends BasicTransformer {

	public ReplaceConstants() {
		super("Replace Constants with Variables");
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (node.getBody() instanceof Rewrite) {
			ConstantsReplaceTransformer crt = new ConstantsReplaceTransformer(
					"");
			Rewrite rew = (Rewrite) node.getBody();
			rew.setLeft((Term) rew.getLeft().accept(crt));
			
			Map<Variable, Constant> newGeneratedSV = crt.getGeneratedSV();
			Term condition = node.getCondition();

			List<Term> terms = new ArrayList<Term>();
			for (Entry<Variable, Constant> entry : newGeneratedSV.entrySet()) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(new KApp(new KInjectedLabel(entry.getKey()), new KList()));
				vars.add(new KApp(new KInjectedLabel(entry.getValue()), new KList()));
				// String sort = entry.getValue().getSort().substring(1);
				String label = "'_==Symbolic_"; //"'_==" + sort + "_";
				terms.add(new KApp(new Constant("KLabel", label), new KList(
						vars)));
			}

			if (terms.isEmpty())
				return node;

			Term newCondition = new KApp(new Constant("KLabel", "'_andBool_"),
					new KList(terms));

			if (condition != null) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(condition);
				vars.add(newCondition);
				newCondition = new KApp(new Constant("KLabel", "'_andBool_"),
						new KList(vars));
			}

			node = node.shallowCopy();
			node.setBody(rew);
			node.setCondition(newCondition);
		}
		return node;
	}
}
