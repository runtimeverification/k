package ro.uaic.info.fmse.transitions.labelify;

import java.util.ArrayList;

import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.KApp;
import ro.uaic.info.fmse.k.ListOfK;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.parsing.Visitor;

public class KAppVisitor extends Visitor {
	public Term kappTerm;

	@Override
	public void visit(ASTNode astNode) {
		if (astNode instanceof TermCons) {
			TermCons tc = (TermCons) astNode;
			Production ppp = DefinitionHelper.conses.get("\"" + tc.getCons() + "\"");
			String klabel = ppp.getLabel();
			Term tempChildren;
			if (tc.getContents().size() == 0)
				tempChildren = new Empty(tc.getLocation(), tc.getFilename(), "List{K}");
			else if (tc.getContents().size() == 1) {
				KAppVisitor tempKapp = new KAppVisitor();
				Term trm = tc.getContents().get(0);
				trm.accept(tempKapp);
				tempChildren = tempKapp.kappTerm;
			} else {
				java.util.List<Term> tempChildrenList = new ArrayList<Term>();
				for (Term term : tc.getContents()) {
					KAppVisitor tempKapp = new KAppVisitor();
					term.accept(tempKapp);
					tempChildren = tempKapp.kappTerm;
				}
				tempChildren = new ListOfK(tc.getLocation(), tc.getFilename(), tempChildrenList);
			}
			kappTerm = new KApp(tc.getLocation(), tc.getFilename(), new Constant(tc.getLocation(), tc.getFilename(), "KLabel", klabel), tempChildren);
		} else {
			String l = astNode.getLocation();
			String f = astNode.getFilename();
			kappTerm = new KApp(l, f, new Constant(l, f, "KLabel", "NAN"), new Empty(l, f, "List{K}"));
		}
	}
}

/*
 * f(5)
 * 
 * 'f(# 5(.List{K}))
 * 
 * env(X |-> 5) 'env(Map2KLabel(C |-> 5)(.List{K}))
 */
