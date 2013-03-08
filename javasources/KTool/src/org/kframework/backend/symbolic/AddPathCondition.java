package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
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

public class AddPathCondition extends BasicTransformer {

	public AddPathCondition() {
		super("Add Path Condition to each rule");
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		
		if (node.getCondition() == null)
			return node;
		
		ConditionTransformer ct = new ConditionTransformer();
		Term condition = (Term) node.getCondition().accept(ct);
		if (ct.getFilteredTerms().isEmpty())
			return node;
		
		if (node.getBody() instanceof Rewrite && node.getAttribute(SymbolicBackend.SYMBOLIC) != null)
		{
			Rewrite rew = (Rewrite) node.getBody();
			
			// variable holding the formula
			Variable phi = MetaK.getFreshVar("K");
			
			// create lhs path condition cell
			Term left = rew.getLeft();
			
			// ignore non-bag and non-cell terms
			Cell leftCell = new Cell();
			leftCell.setLabel(MetaK.Constants.pathCondition);
			leftCell.setEllipses(Ellipses.NONE);
			leftCell.setContents(phi);

			
			
			if (left instanceof Cell) {
				AddConditionToConfig.addCellNextToKCell((Cell)left, leftCell);
			}
			

			// create rhs path condition cell 
			Term right = rew.getRight();

			Cell rightCell = new Cell();
			rightCell.setLabel(MetaK.Constants.pathCondition);
			rightCell.setEllipses(Ellipses.NONE);
			List<Term> list = new ArrayList<Term>();
			list.add(phi);
			list.add(andBool(ct.getFilteredTerms()));
			Term pathCondition = new KApp(Constant.BOOL_ANDBOOL_KLABEL, new KList(list));
			rightCell.setContents(pathCondition);

			if (right instanceof Cell) {
				AddConditionToConfig.addCellNextToKCell((Cell)right, rightCell);
			}
			
			List<Term> myList = new ArrayList<Term>();
			myList.add(condition);
			myList.add(checkSat(pathCondition));
			Term cond = new KApp(Constant.ANDBOOL_KLABEL, new KList(myList));
			
			// add transition attribute
			List<Attribute> attrs = node.getAttributes().getContents();
			// bad practice
			attrs.add(new Attribute("transition", ""));
			
			Attributes atts = node.getAttributes().shallowCopy();
			atts.setContents(attrs);

			
			// re-construct the rule
			node = node.shallowCopy();
			node.setBody(new Rewrite(left, right));
			node.setAttributes(atts);
//			node.setCondition(Constant.TRUE);
			node.setCondition(cond);
		}
		
		return node;
	}

	private Term andBool(List<Term> filteredTerms) {

		Iterator<Term> it = filteredTerms.iterator();
		Term and = it.next();
		while(it.hasNext())
		{
			List<Term> list = new ArrayList<Term>();
			list.add(and);
			list.add(it.next());
			and = new KApp(Constant.BOOL_ANDBOOL_KLABEL, new KList(list));
		}
		return and;
	}

	private Term checkSat(Term pathCondition) {
		// checkSat(pathCondition) =/=K # "unsat"(.KList)
		KApp unsat = new KApp(new KInjectedLabel(Constant.STRING("unsat")), new KList());
		KApp checkSat = new KApp(Constant.KLABEL("'checkSat"), pathCondition);
		List<Term> items = new ArrayList<Term>();
		items.add(unsat);
		items.add(checkSat);
		return new KApp(Constant.KNEQ_KLABEL, new KList(items));
	}
}
