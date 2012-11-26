package org.kframework.krun;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class ConcretizeSyntax extends CopyOnWriteTransformer {

	private String sortContext = "K";
	private List<Term> subst;

	public ConcretizeSyntax() {
		super("Abstract K to Syntax K");
	}

	@Override
	public ASTNode transform(KApp kapp) throws TransformerException {
		Term label = kapp.getLabel();
		Term child = kapp.getChild();
		if (label instanceof KInjectedLabel && child instanceof Empty) {
			Term injected = ((KInjectedLabel)label).getTerm();
			if (MetaK.isBuiltinSort(injected.getSort()) || DefinitionHelper.isSubsortedEq(sortContext, injected.getSort())) {
				return (Term)injected.accept(this);
			}
		} else if (label instanceof Constant) {
			Set<String> conses = DefinitionHelper.labels.get(((Constant)label).getValue());
			Set<String> validConses = new HashSet<String>();
			List<Term> contents = new ArrayList<Term>();
			List<Term> possibleTerms = new ArrayList<Term>();
			if (child instanceof ListOfK) {
				contents = ((ListOfK)child).getContents();
			} else if (!(child instanceof Empty)) {
				contents.add(child);
			}
			if (conses != null) {	
				for (String cons : conses) {
					Production p = DefinitionHelper.conses.get(cons);

					if ((DefinitionHelper.isSubsortedEq(sortContext, p.getSort()) || sortContext.equals("K")) && p.getArity() == contents.size()) {
						validConses.add(cons);
						for (int i = 0; i < contents.size(); i++) {
							String temp = sortContext;
							sortContext = p.getChildSort(i);
							contents.set(i, (Term)contents.get(i).accept(this));
							sortContext = temp;
						}
					}
				}
				for (String cons : validConses) {
					Production p = DefinitionHelper.conses.get(cons);
					possibleTerms.add(new TermCons(p.getSort(), cons, contents));
				}
				if (possibleTerms.size() == 0) {
					return super.transform(kapp);
				}
				if (possibleTerms.size() == 1) {
					return possibleTerms.get(0);
				} else {
					
					return new Ambiguity(sortContext, possibleTerms);
				}
			} else {
				//could be a list terminator, which don't have conses
				//String value = ((Constant)label).getValue
			}
		} else if (label instanceof Freezer) {
			subst = new ArrayList<Term>();
			if (child instanceof ListOfK) {
				subst = ((ListOfK)child).getContents();
			} else if (!(child instanceof Empty)) {
				subst.add(child);
			}
			return ((Freezer)label).getTerm().accept(this);
		}
		return super.transform(kapp);
	}

	@Override
	public ASTNode transform(KSequence i) throws TransformerException {
		String temp = sortContext;
		sortContext = "K";
		ASTNode result = super.transform(i);
		sortContext = temp;
		return result;
	}

	@Override
	public ASTNode transform(BagItem i) throws TransformerException {
		String temp = sortContext;
		sortContext = "K";
		ASTNode result = super.transform(i);
		sortContext = temp;
		return result;
	}

	@Override
	public ASTNode transform(SetItem i) throws TransformerException {
		String temp = sortContext;
		sortContext = "K";
		ASTNode result = super.transform(i);
		sortContext = temp;
		return result;
	}

	@Override
	public ASTNode transform(ListItem i) throws TransformerException {
		String temp = sortContext;
		sortContext = "K";
		ASTNode result = super.transform(i);
		sortContext = temp;
		return result;
	}

	@Override
	public ASTNode transform(MapItem i) throws TransformerException {
		String temp = sortContext;
		sortContext = "K";
		ASTNode result = super.transform(i);
		sortContext = temp;
		return result;
	}

	@Override
	public ASTNode transform(FreezerVariable var) throws TransformerException {
		for (Term t : subst) {
			KApp app = (KApp)t;
			String name = ((FreezerSubstitution)app.getLabel()).getName();
			if (name.equals(var.getName())) {
				return app.getChild().accept(this);
			}
		}
		return var;
	}
			

}
