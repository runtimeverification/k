package org.kframework.krun;

import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.TypeSystemFilter;
import org.kframework.utils.StringUtil;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

public class ConcretizeSyntax extends CopyOnWriteTransformer {


	public ConcretizeSyntax() {
		super("Abstract K to Syntax K");
	}

	@Override
	public ASTNode transform(KApp kapp) throws TransformerException {
		ASTNode t = internalTransform(kapp);
		try {
			t = t.accept(new TypeSystemFilter());
		} catch (TransformerException e) {
			//type error, so don't disambiguate
		}
		t = t.accept(new RemoveEmptyLists());
		return t;
	}

	public static class RemoveEmptyLists extends CopyOnWriteTransformer {
		public RemoveEmptyLists() {
			super("Reverse AddEmptyLists");
		}

		@Override
		public ASTNode transform(TermCons tcParent) throws TransformerException {
			for (int i = 0; i < tcParent.getContents().size(); i++) {
				Term child = tcParent.getContents().get(i);
				internalTransform(tcParent, i, child);
			}
			return tcParent;
		}

		private void internalTransform(TermCons tcParent, int i, Term child) {
			if (child instanceof TermCons) {
				TermCons termCons = (TermCons) child;
				if (termCons.getProduction().isListDecl()) {
					if (AddEmptyLists.isAddEmptyList(tcParent.getProduction().getChildSort(i), termCons.getContents().get(0).getSort()) && termCons.getContents().get(1) instanceof Empty) {
						
						tcParent.getContents().set(i, termCons.getContents().get(0));
					}
				}
			} else if (child instanceof Ambiguity) {
				Ambiguity amb = (Ambiguity) child;
				for (Term choice : amb.getContents()) {
					internalTransform(tcParent, i, choice);
				}
			}
		}
	}


	public ASTNode internalTransform(KApp kapp) throws TransformerException {
		Term label = kapp.getLabel();
		Term child = kapp.getChild();
		child = child.shallowCopy();
		List<Term> possibleTerms;
		if (label instanceof KInjectedLabel && child.equals(KList.EMPTY)) {
			if (label instanceof FreezerLabel) {
				FreezerLabel l = (FreezerLabel) label;
				return new Freezer((Term)l.getTerm().accept(this));
			}
			Term injected = ((KInjectedLabel)label).getTerm();
			if (injected instanceof Builtin || injected instanceof Token || injected instanceof Constant) {
				return (Term)injected.accept(this);
			}
		} else if (label instanceof KLabelConstant) {
			String klabel = ((KLabelConstant) label).getLabel();
			Set<String> conses = DefinitionHelper.labels.get(klabel);
			List<Term> contents = new ArrayList<Term>();
			possibleTerms = new ArrayList<Term>();
			if (child instanceof KList) {
				contents = ((KList)child).getContents();
			} else if (!(child.equals(KList.EMPTY))) {
				contents.add(child);
			}
			if (conses != null) {	
				for (int i = 0; i < contents.size(); i++) {
					contents.set(i, (Term)contents.get(i).accept(this));
				}
				for (String cons : conses) {
					Production p = DefinitionHelper.conses.get(cons);
					List<Term> newContents = new ArrayList<Term>(contents);
					if (p.getAttribute("reject") != null)
						continue;
					if (p.getArity() != contents.size())
						continue;
					for (int i = 0; i < contents.size(); i++) {
						if (contents.get(i) instanceof KApp && ((KApp)contents.get(i)).getLabel() instanceof KInjectedLabel) {
							KInjectedLabel l = (KInjectedLabel)((KApp)contents.get(i)).getLabel();
							if (DefinitionHelper.isSubsortedEq(p.getChildSort(i), l.getTerm().getSort())) {
								newContents.set(i, l.getTerm());
							}
						} else {
							newContents.set(i, newContents.get(i).shallowCopy());
						}
					}
					possibleTerms.add(new TermCons(p.getSort(), cons, newContents));
				}
				if (possibleTerms.size() == 0) {
					return super.transform(kapp);
				}
				if (possibleTerms.size() == 1) {
					return possibleTerms.get(0);
				} else {
					return new Ambiguity("K", possibleTerms);
				}
			} else if (child instanceof Empty) {
				//could be a list terminator, which don't have conses
				Set<String> sorts = DefinitionHelper.listLabels.get(klabel);
				possibleTerms = new ArrayList<Term>();
				if (sorts != null) {
					for (String sort : sorts) {
							possibleTerms.add(new Empty(sort));
					}
					if (possibleTerms.size() == 0) {
						return super.transform(kapp);
					}
					if (possibleTerms.size() == 1) {
						return possibleTerms.get(0);
					} else {
						
						return new Ambiguity("K", possibleTerms);
					}
				}
			} else if (klabel.equals("#token")) {
				if (contents.size() != 2) {
					return super.transform(kapp);
				}
				ASTNode sortNode = contents.get(0).accept(this);
				ASTNode valueNode = contents.get(1).accept(this);
				if (!(sortNode instanceof StringBuiltin && valueNode instanceof StringBuiltin)) {
					return super.transform(kapp);
				}
				StringBuiltin sort = (StringBuiltin) sortNode;
				StringBuiltin value = (StringBuiltin) valueNode;

				String escapedSort = sort.getValue();
				String escapedValue = value.getValue();
				escapedSort = escapedSort.substring(1, escapedSort.length() - 1);
				escapedValue = escapedValue.substring(1, escapedValue.length() - 1);
				return new Constant(StringUtil.unescape(escapedSort), StringUtil.unescape(escapedValue));
			}
		}
		return super.transform(kapp);
	}

	@Override
	public ASTNode transform(Cell cell) throws TransformerException {
		if (cell.getLabel().matches(".*-fragment")) {
			return cell.getContents().accept(this);
		}
		return super.transform(cell);
	}

	@Override
	public ASTNode transform(Bag bag) throws TransformerException {
		List<Term> contents = new ArrayList<Term>();
		for (Term child : bag.getContents()) {
			Term accept = (Term) child.accept(this);
			if (accept instanceof Empty) {
				Empty empty = (Empty) accept;
				if (!empty.getSort().equals("Bag")) {
					contents.add(accept);
				}
			} else {
				contents.add(accept);
			}
		}
		if (contents.size() == 0) {
			return new Empty("Bag");
		}
		if (contents.size() == 1) {
			return contents.get(0);
		}
		return new Bag(contents);
	}
}
