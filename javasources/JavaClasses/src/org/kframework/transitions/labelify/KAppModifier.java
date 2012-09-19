package org.kframework.transitions.labelify;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Constant;
import org.kframework.k.Empty;
import org.kframework.k.KApp;
import org.kframework.k.KInjectedLabel;
import org.kframework.k.ListOfK;
import org.kframework.k.Production;
import org.kframework.k.TermCons;
import org.kframework.loader.DefinitionHelper;
import org.kframework.transitions.maude.MaudeHelper;
import org.kframework.visitors.BasicTransformer;

public class KAppModifier extends BasicTransformer {
	public KAppModifier() {
		super("Syntax K to Abstract K");
	}

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
