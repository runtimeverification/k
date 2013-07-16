package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.KList;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddImplicationRules extends CopyOnWriteTransformer {

	public static final String IMPLRULE_ATTR = "implication-rule";
	private List<ASTNode> reachabilityRules;

	public AddImplicationRules(Context context, List<ASTNode> reachabilityRules) {
		super("Add rules for implication", context);
		this.reachabilityRules = reachabilityRules;
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
	
		List<ModuleItem> items = node.getItems();
		node = node.shallowCopy();
		node.setItems(items);
		
		
		for (ASTNode rr : reachabilityRules) {
			if (rr instanceof Sentence) {
				Sentence r = (Sentence) rr;
				
				ReachabilityRuleKILParser parser = new ReachabilityRuleKILParser(
						context);
				r.accept(parser);

				Term newPi = parser.getPi().shallowCopy();
				Term implies = getFreshImplication(reachabilityRules.indexOf(rr), context);
				SetCellContent app = new SetCellContent(context, implies, "k");
				newPi = (Term) newPi.accept(app);

				
				Term newPiPrime = parser.getPi_prime();
				SetCellContent appPrime = new SetCellContent(context, KList.EMPTY, "k");
				newPiPrime = (Term) newPiPrime.accept(appPrime);

				Rule implicationRule = new Rule(newPi, newPiPrime, context);
				int correspondingIndex = reachabilityRules.indexOf(rr);
				implicationRule.addAttribute(IMPLRULE_ATTR, correspondingIndex + "");
				
				items.add(implicationRule);
			}
		}
		
		return node;
	}

	public static Term getFreshImplication(int indexOf, Context context) {
		return new AddSymbolicK(context).freshSymSortId("#Id", "implies" + indexOf); 
	}
}
