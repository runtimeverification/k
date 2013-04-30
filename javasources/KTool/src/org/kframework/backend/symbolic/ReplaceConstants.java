package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.compile.transformers.AddPredicates;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Builtin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * * This is part of the symbolic transformation: replace each (data) constant
 * with a symbolic value and add an equality in the side condition of the rule.
 * 
 * @author andreiarusoaie
 */
public class ReplaceConstants extends CopyOnWriteTransformer {

	public ReplaceConstants() {
		super("Replace Constants with Variables");
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (!node.containsAttribute(SymbolicBackend.SYMBOLIC)) {
			return node;
		}

		if (node.getBody() instanceof Rewrite) {
			ConstantsReplaceTransformer crt = new ConstantsReplaceTransformer(
					"");
			Rewrite rew = (Rewrite) node.getBody();
			rew.setLeft((Term) rew.getLeft().accept(crt));

			Map<Variable, Builtin> newGeneratedSV = crt.getGeneratedSV();
			Term condition = node.getCondition();

			List<Term> terms = new ArrayList<Term>();
			for (Entry<Variable, Builtin> entry : newGeneratedSV.entrySet()) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(entry.getKey());
				vars.add(KApp.of(new KInjectedLabel(entry.getValue())));

				terms.add(new KApp(KLabelConstant.of(KLabelConstant.KEQ.getLabel()), new KList(vars)));

				terms.add(KApp.of(
                        KLabelConstant.of(AddPredicates.predicate(
                                entry.getValue().getSort().replaceFirst("#", ""))),
                        entry.getKey()));
			}

			if (terms.isEmpty())
				return node;

			Term newCondition = new KApp(KLabelConstant.ANDBOOL_KLABEL, new KList(
					terms));

			if (condition != null) {
				List<Term> vars = new ArrayList<Term>();
				vars.add(condition);
				vars.add(newCondition);
				newCondition = new KApp(KLabelConstant.ANDBOOL_KLABEL,
						new KList(vars));
			}

			node = node.shallowCopy();
			node.setBody(rew);
			node.setCondition(newCondition);
		}
		return node;
	}
}
