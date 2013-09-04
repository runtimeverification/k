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
		
		if(node.getAttribute(AddCircularityRules.RRULE_ATTR)!= null && (node.getBody() instanceof Rewrite)) {
			
			Rewrite rewrite = (Rewrite) node.getBody();
			int rIndex = Integer.parseInt(node.getAttribute(AddCircularityRules.RRULE_ATTR));
			
			// get the corresponding reachability rule
			ASTNode rrule = reachabilityRules.get(rIndex);
			ReachabilityRuleKILParser parser = new ReachabilityRuleKILParser(context);
			rrule.accept(parser);
			
			//TODO: how about ensures?
			
			// remove the condition wrapper
			Term cnd = node.getRequires().shallowCopy();
			ExtractPatternless ep = new ExtractPatternless(context, true);
			cnd = (Term) cnd.accept(ep);
			
			// create the new rule
			Term left = rewrite.getLeft();
			Term right = rewrite.getRight();
			
			ExtractCellContent ecc = new ExtractCellContent(context, "k");
			left.accept(ecc);
			KSequence kseq = (KSequence) ecc.getContent();
			List<Term> contents = kseq.getContents();
			
			List<Term> newContents = new ArrayList<Term>();
			newContents.add(contents.get(0).shallowCopy());
			Term pgmprime = contents.get(1).shallowCopy(); // collect the program without label
			newContents.add(contents.get(2).shallowCopy());
			KSequence newSeq = new KSequence(newContents);
			
			Term newLeft = left.shallowCopy();
			newLeft = (Term) newLeft.accept(new SetCellContent(context, newSeq, "k"));
			Term newRight = right.shallowCopy();
			Rule newRule = new Rule(newLeft, newRight, context);
			newRule.setRequires(cnd);
			newRule.setAttributes(node.getAttributes().shallowCopy());
			
			// get program without the first label
			Term newPgm = left.shallowCopy();
			
			// create implication term
			Term implies = AddCheckConstants.getFreshImplicationForPgm(rIndex, context);
			
			// set PGM ~> implies in the <k> cell
			List<Term> cnt = new ArrayList<Term>();
			cnt.add(pgmprime);
			cnt.add(implies);
			KSequence newContent = new KSequence(cnt);
			
			SetCellContent scc = new SetCellContent(context, newContent, "k");
			newPgm = (Term) newPgm.accept(scc);

			SetCellContent setpc = new SetCellContent(context, ep.getPhi(), MetaK.Constants.pathCondition);
			newPgm = (Term) newPgm.accept(setpc);
			
			// generate fresh symbolic variables
			VariablesVisitor vvleft = new VariablesVisitor(context);
			parser.getPi().accept(vvleft);

//			System.out.println("VARIABLES: " + vvleft.getVariables());
			
//			System.out.println("PI: " + newPi);
			MakeFreshVariables mfv = new MakeFreshVariables(context, vvleft.getVariables());
			newPgm = (Term) newPgm.accept(mfv);
			
//			newPi = (Term) newPi.accept(new FlattenSyntax(context));
//			System.out.println("PGM: " + newPi);
			
			programs.add(newPgm);
			
			return newRule;
		}
		
		return super.transform(node);
	}

	public List<Term> getPrograms() {
		return programs;
	}
}
