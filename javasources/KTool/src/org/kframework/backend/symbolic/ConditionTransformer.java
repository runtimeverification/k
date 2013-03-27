package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
/**
 * Filter the rule side condition such that it contains only
 * SMTLIB translatable items. The filtered terms are stored
 * in a list for further use.
 * @author andreiarusoaie
 *
 */
public class ConditionTransformer extends CopyOnWriteTransformer  {

	List<Term> filteredTerms = new ArrayList<Term>();
	
	public ConditionTransformer() {
		super("Filter side conditions");
	}

	@Override
	public ASTNode transform(KApp node) throws TransformerException {
		Term label = node.getLabel();
		if (label instanceof Constant) {
			String name = ((Constant) label).getValue();
			Term content = node.getChild();
			if (name.equals(Constant.ANDBOOL_KLABEL.getValue()))
			{
				if (content instanceof KList) {
					List<Term> terms = ((KList) content).getContents();
					List<Term> remainingTerms = new ArrayList<Term>();
					for(Term t : terms) {
						CheckSmtlibVisitor csv = new CheckSmtlibVisitor();
						t.accept(csv);
						if (csv.smtValid())
							filteredTerms.add(t.shallowCopy());
						else remainingTerms.add(t.shallowCopy());
					}
					content = new KList(remainingTerms);
				}
			}
			else {
				CheckSmtlibVisitor csv = new CheckSmtlibVisitor();
				content.accept(csv);
				if (csv.smtValid())
				{
					filteredTerms.add(content.shallowCopy());
					content = new KList();
				}
				
			}
			
			node = node.shallowCopy();
			node.setChild(content);
			return node;
		}
	
		return super.transform(node);
	}
	
	public List<Term> getFilteredTerms() {
		return filteredTerms;
	}
}
