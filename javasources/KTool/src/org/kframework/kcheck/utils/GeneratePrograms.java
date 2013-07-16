package org.kframework.kcheck.utils;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.KSequence;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class GeneratePrograms extends BasicTransformer {

	private List<ASTNode> reachabilityRules;
	private List<Term> programs;
	
	public GeneratePrograms(Context context, List<ASTNode> reachabilityRules) {
		super("Generate reachability programs.", context);
		this.reachabilityRules = reachabilityRules;
		programs = new ArrayList<Term>();
	}
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		
		if(node.getAttribute(AddImplicationRules.IMPLRULE_ATTR) != null && (node.getBody() instanceof Rewrite)) {
			
			Rewrite rewrite = (Rewrite) node.getBody();
			int rIndex = Integer.parseInt(node.getAttribute(AddImplicationRules.IMPLRULE_ATTR));
			
			// get the corresponding reachability rule
			ASTNode rrule = reachabilityRules.get(rIndex);
			ReachabilityRuleKILParser parser = new ReachabilityRuleKILParser(context);
			rrule.accept(parser);

			// process program
			Term pi = parser.getPi();
			ExtractCellContent kcell = new ExtractCellContent(context, "k");
			pi.accept(kcell);
			Term pgm = kcell.getContent();
			RemoveLabel pl = new RemoveLabel(context);
			pgm = (Term) pgm.accept(pl);
			
			// create implication term
			Term implies = AddImplicationRules.getFreshImplication(rIndex, context);

			// set PGM ~> implies in the <k> cell
			Term newPi = rewrite.getLeft().shallowCopy();
			List<Term> cnt = new ArrayList<Term>();
			cnt.add(pgm);
			cnt.add(implies);
			KSequence newContent = new KSequence(cnt);
			SetCellContent seq = new SetCellContent(context, newContent, "k");
			newPi = (Term) newPi.accept(seq);

			SetCellContent setpc = new SetCellContent(context, parser.getPhi(), MetaK.Constants.pathCondition);
			newPi = (Term) newPi.accept(setpc);
			
			// generate fresh symbolic variables
			VariablesVisitor vvleft = new VariablesVisitor(context);
			newPi.accept(vvleft);

//			System.out.println("PI: " + newPi);
			MakeFreshVariables mfv = new MakeFreshVariables(context, vvleft.getVariables());
			newPi = (Term) newPi.accept(mfv);
			
			programs.add(newPi);
//			System.out.println("NEWPI: " + newPi);
		}
		
		return super.transform(node);
	}

	public List<Term> getPrograms() {
		return programs;
	}
}
