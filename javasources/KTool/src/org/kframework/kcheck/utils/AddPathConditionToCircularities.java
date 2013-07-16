package org.kframework.kcheck.utils;

import java.util.List;

import org.kframework.backend.symbolic.AddConditionToConfig;
import org.kframework.backend.symbolic.AddPathCondition;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddPathConditionToCircularities extends CopyOnWriteTransformer {

	private List<ASTNode> reachabilityRules;

	public AddPathConditionToCircularities(Context context, List<ASTNode> reachabilityRules) {
		super("Add path condition to circularities", context);
		this.reachabilityRules = reachabilityRules;
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		
		if(node.getAttribute(AddCircularityRules.RRULE_ATTR) != null && (node.getBody() instanceof Rewrite)) {

			// get the corresponding reachability rule
			int rIndex = Integer.parseInt(node.getAttribute(AddCircularityRules.RRULE_ATTR)); 
			ASTNode rrule = reachabilityRules.get(rIndex);
			ReachabilityRuleKILParser parser = new ReachabilityRuleKILParser(context);
			rrule.accept(parser);
			
			// separate left and right
			Rewrite ruleBody = (Rewrite) node.getBody();
			Term left = ruleBody.getLeft().shallowCopy();
			Term right = ruleBody.getRight().shallowCopy();
			
			
			// create lhs path condition cell
			Variable psi = Variable.getFreshVar("K");
            Cell leftCell = new Cell();
            leftCell.setLabel(MetaK.Constants.pathCondition);
            leftCell.setEllipses(Ellipses.NONE);
            leftCell.setContents(psi);
			left = AddConditionToConfig.addSubcellToCell((Cell)left, leftCell);

			// create rhs path condition cell
            Cell rightCell = new Cell();
            rightCell.setLabel(MetaK.Constants.pathCondition);
            rightCell.setEllipses(Ellipses.NONE);
            rightCell.setContents(KApp.of(KLabelConstant.ANDBOOL_KLABEL, psi, parser.getPhi(), parser.getPhi_prime()));
			right = AddConditionToConfig.addSubcellToCell((Cell)right, rightCell);

			// condition
			Term condition = node.getCondition().shallowCopy();

			Term implication = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, psi, KApp.of(KLabelConstant.NOTBOOL_KLABEL, parser.getPhi()));
			KApp unsat = StringBuiltin.kAppOf("unsat");
	        KApp checkSat = KApp.of(KLabelConstant.of("'checkSat", context), implication);
	        implication = KApp.of(KLabelConstant.KEQ_KLABEL, checkSat, unsat);
	        
			Term pc = KApp.of(KLabelConstant.BOOL_ANDBOOL_KLABEL, psi, parser.getPhi_prime());
			pc = AddPathCondition.checkSat(pc, context);
			
			Rule newRule = new Rule(left, right, context);
			newRule.setCondition(KApp.of(KLabelConstant.ANDBOOL_KLABEL, condition, implication, pc));
			newRule.setAttributes(node.getAttributes().shallowCopy());
			return newRule;
		}
		
		return super.transform(node);
	}
}
