package ro.uaic.info.fmse.transitions.labelify;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.KApp;
import ro.uaic.info.fmse.k.KInjectedLabel;
import ro.uaic.info.fmse.k.ListOfK;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.transitions.maude.MaudeHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class KAppModifier extends BasicTransformer {
	public ASTNode transform(TermCons tc) throws TransformerException {
		String l = tc.getLocation();
		String f = tc.getFilename();
		Production ppp = DefinitionHelper.conses.get(tc.getCons());
		String klabel = ppp.getKLabel();
		KApp kapp = new KApp(l, f);
		kapp.setLabel(new Constant(l, f, "KLabel", klabel));
		if (tc.getContents().size() == 0)
			kapp.setChild(new Empty(l, f, "List{K}"));
		else if (tc.getContents().size() == 1) {
			kapp.setChild(tc.getContents().get(0));
		} else {
			ListOfK lok = new ListOfK(l, f);
			lok.setContents(tc.getContents());
			kapp.setChild(lok);
		}
		return kapp.accept(this);
	}

	public ASTNode transform(Constant cst) {
		String l = cst.getLocation();
		String f = cst.getFilename();

		if (!cst.getSort().equals("KLabel"))
			return new KApp(l, f, new KInjectedLabel(cst), new Empty(l, f, "List{K}"));

		return cst;
	}

	public ASTNode transform(Empty emp) {
		String l = emp.getLocation();
		String f = emp.getFilename();
		// if this is a list sort
		if (!MaudeHelper.basicSorts.contains(emp.getSort())) {
			Constant cst = new Constant(l, f, "KLabel", "'." + emp.getSort() + "");
			return new KApp(l, f, cst, new Empty(l, f, "List{K}"));
		}
		return emp;
	}
}

/*
 * f(5)
 * 
 * 'f(# 5(.List{K}))
 * 
 * env(X |-> 5) 'env(Map2KLabel(C |-> 5)(.List{K}))
 */
