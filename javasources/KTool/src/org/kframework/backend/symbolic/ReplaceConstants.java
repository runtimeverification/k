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

public class ReplaceConstants extends BasicTransformer {

	public ReplaceConstants(String name) {
		super(name);
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (node.getBody() instanceof Rewrite) {
			ConstantsReplaceTransformer crt = new ConstantsReplaceTransformer(
					"");
			Rewrite rew = (Rewrite) node.getBody();
			System.out.println("BEFORE: " + rew.getLeft());
			rew.setLeft((Term) crt.transform(rew.getLeft()));
			System.out.println("AFTER : " + rew.getLeft());
			Map<Variable, Constant> newGeneratedSV = crt.getGeneratedSV();
			Term condition = node.getCondition();

			List<Term> terms = new ArrayList<Term>();
			Term newCondition = new KApp(new Constant("KLabel", "'_andBool_"),
					new KList(terms));

			for (Entry<Variable, Constant> entry : newGeneratedSV.entrySet()) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(entry.getKey());
				vars.add(entry.getValue());
				terms.add(new KApp(new Constant("KLabel", "'_==K_"), new KList(
						vars)));
			}

			if (condition != null) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(condition);
				vars.add(newCondition);
				newCondition = new KApp(new Constant("KLabel", "'_andBool_"),
						new KList(vars));
			}

			node.setBody(rew);
			node.setCondition(newCondition);
		}
		return node;
	}
}
