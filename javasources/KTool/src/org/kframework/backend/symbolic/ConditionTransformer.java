package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

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
			if (name.equals(Constant.ANDBOOL_KLABEL.getValue()))
			{
				return super.transform(node);		
			}

			if (name.equals(Constant.BOOL_ANDBOOL_KLABEL.getValue()))
			{
				node.setLabel(Constant.ANDBOOL_KLABEL);
				return super.transform(node);
			}
			
			if (MetaK.isPredefinedPredicate(name))
			{
				return node;
			}
		}
		
		filteredTerms.add(node);
		return null;
	}
	
	public List<Term> getFilteredTerms() {
		return filteredTerms;
	}
}
