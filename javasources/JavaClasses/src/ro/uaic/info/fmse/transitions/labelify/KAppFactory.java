package ro.uaic.info.fmse.transitions.labelify;

import java.util.ArrayList;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.parsing.ASTNode;

public class KAppFactory {
	public Term kappTerm;

	public static ASTNode getTerm(ASTNode astNode) {
		String l = astNode.getLocation();
		String f = astNode.getFilename();
		if (astNode instanceof TermCons) {
			TermCons tc = (TermCons) astNode;
			Production ppp = DefinitionHelper.conses.get("\"" + tc.getCons() + "\"");
			String klabel = ppp.getLabel();
			Term tempChildren;
			if (tc.getContents().size() == 0)
				tempChildren = new Empty(l, f, "List{K}");
			else if (tc.getContents().size() == 1) {
				tempChildren = (Term) KAppFactory.getTerm(tc.getContents().get(0));
			} else {
				java.util.List<Term> tempChildrenList = new ArrayList<Term>();
				for (Term term : tc.getContents()) {
					tempChildrenList.add((Term) KAppFactory.getTerm(term));
				}
				ListOfK lok = new ListOfK(l, f);
				lok.setContents(tempChildrenList);
				tempChildren = lok;
			}
			return new KApp(l, f, new Constant(l, f, "KLabel", klabel), tempChildren);
		} else if (astNode instanceof Bag) {
			Bag term1 = (Bag) astNode;
			Bag term2 = new Bag(l, f);
			java.util.List<Term> tempChildrenList = new ArrayList<Term>();
			for (Term trm : term1.getContents()) {
				tempChildrenList.add((Term) KAppFactory.getTerm(trm));
			}
			term2.setContents(tempChildrenList);
			return term2;
		} else if (astNode instanceof BagItem) {
			BagItem term1 = (BagItem) astNode;
			BagItem term2 = new BagItem(l, f);
			term2.setItem((Term) KAppFactory.getTerm(term1));
			return term2;
		} else if (astNode instanceof Configuration) {
			Configuration term1 = (Configuration) astNode;
			Configuration term2 = new Configuration(l, f);

			term2.setAttributes(term1.getAttributes());
			term2.setBody((Term) KAppFactory.getTerm(term1.getBody()));
			term2.setCondition(null);

			return term2;
		} else if (astNode instanceof Constant) {
			Constant term1 = (Constant) astNode;
			Constant term2 = new Constant(l, f);
			Empty empty = new Empty(l, f, "List{K}");

			if (term1.getSort().equals("KLabel")) {
				term2.setSort(term1.getSort());
				term2.setValue(term1.getValue());
				return term2;
			} else if (term1.getSort().equals("#Id")) {
				KApp term3 = new KApp(l, f);
				KApp term4 = new KApp(l, f);
				term3.setLabel(term4);
				term3.setChild(empty);
				term4.setLabel(new Constant(l, f, "KLabel", "#id_"));
				term4.setChild(new Constant(l, f, term1.getSort(), "\"" + term1.getValue() + "\""));
				return term3;
			} else if (term1.getSort().equals("#String") || term1.getSort().equals("#Int") || term1.getSort().equals("#Float") || term1.getSort().equals("#Bool")) {
				KApp term3 = new KApp(l, f);
				KApp term4 = new KApp(l, f);
				term3.setLabel(term4);
				term3.setChild(empty);
				term4.setLabel(new Constant(l, f, "KLabel", "#_"));
				term4.setChild(new Constant(l, f, term1.getSort(), term1.getValue()));
				return term3;
			}
			return null;
		} else if (astNode instanceof Empty) {
			Configuration term1 = (Configuration) astNode;
			Configuration term2 = new Configuration(l, f);

			term2.setAttributes(term1.getAttributes());
			term2.setBody((Term) KAppFactory.getTerm(term1.getBody()));
			term2.setCondition(null);

			return term2;
		}

		System.out.println(">>> " + astNode + " <<< - unimplemented yet: KAppFactory");
		return new Empty(l, f, "List{K}");
	}
}

/*
 * f(5)
 * 
 * 'f(# 5(.List{K}))
 * 
 * env(X |-> 5) 'env(Map2KLabel(C |-> 5)(.List{K}))
 */
