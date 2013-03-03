package org.kframework.backend.unparser;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Stack;

public class AddBracketsFilter extends CopyOnWriteTransformer {

	public AddBracketsFilter() {
		super("Add brackets");
	}

	@Override	
	public ASTNode transform(TermCons ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(Collection ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(MapItem ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(Cell ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(CollectionItem ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(KApp ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(Hole ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(Freezer ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	@Override	
	public ASTNode transform(KInjectedLabel ast) throws TransformerException {
		prepare(ast);
		ASTNode result = super.transform(ast);
		boolean needsParens = postpare();
		if (needsParens)
			return new Bracket((Term)result);
		return result;
	}

	private enum Associativity {
		LEFT,
		RIGHT,
		NONASSOC,
		ASSOC,
		NONE;

		public boolean equals2(Associativity o) {
			return this == o || this == NONE || o == NONE;
		}
	}

	private enum Fixity {
		BARE_LEFT,
		BARE_RIGHT
	}

	private boolean isUnary(Term t) {
		if (t instanceof TermCons) {
			TermCons tc = (TermCons) t;
			return tc.getProduction().getArity() == 1;
		} else if (t instanceof MapItem) {
			return false;
		} else if (t instanceof CollectionItem) {
			return true;
		} else if (t instanceof Cell || t instanceof Freezer || t instanceof KInjectedLabel) {
			return true;
		}
		return false;
	}

	private Associativity getAssociativity(Term t) {
		if (t instanceof TermCons) {
			TermCons tc = (TermCons)t;
			Production p = tc.getProduction();
			if (p.isListDecl()) 
				return Associativity.RIGHT;
			if (p.getAttributes().containsKey("left"))
				return Associativity.LEFT;
			if (p.getAttributes().containsKey("right"))
				return Associativity.RIGHT;
			if (p.getAttributes().containsKey("non-assoc"))
				return Associativity.NONASSOC;
		} else if (t instanceof Collection) {
			return Associativity.ASSOC;
		}
		return Associativity.NONE;
	}

	private boolean isAtom(Term inner) {
		if (inner instanceof Constant) return true;
		if (inner instanceof Empty) return true;
		if (inner instanceof FreezerHole) return true;
		if (inner instanceof Hole) return true;
		if (inner instanceof Variable) return true;
		if (inner instanceof TermCons) {
			TermCons tc = (TermCons) inner;
			if (tc.getProduction().getArity() == 0) return true;
		}
		return false;
	}

	/** compute fixity of single production */
	private EnumSet<Fixity> getFixity(Term t) {
		if (t instanceof TermCons) {
			TermCons tc = (TermCons) t;
			Production p = tc.getProduction();
			EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
			if (p.getItems().get(0).getType() != ProductionType.TERMINAL)
				set.add(Fixity.BARE_LEFT);
			if (p.getItems().get(p.getItems().size() - 1).getType() != ProductionType.TERMINAL)
				set.add(Fixity.BARE_RIGHT);
			return set;
		} else if (t instanceof Collection || t instanceof MapItem || t instanceof Freezer) {
			return EnumSet.allOf(Fixity.class);
		} else if (t instanceof CollectionItem || t instanceof Cell) {
			return EnumSet.noneOf(Fixity.class);
		} else if (t instanceof KApp) {
			return EnumSet.of(Fixity.BARE_LEFT);
		} else if (t instanceof KInjectedLabel) {
			return EnumSet.of(Fixity.BARE_RIGHT);
		}
		throw new UnsupportedOperationException("term fixity");
	}

	private EnumSet<Fixity> getPosition(Term inner, Term outer) {
		List<Term> childTerms;
		EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
		if (outer instanceof TermCons) {
			TermCons tc = (TermCons)outer;
			childTerms = tc.getContents();
		} else if (outer instanceof Collection) {
			Collection c = (Collection)outer;
			childTerms = c.getContents();
		} else if (outer instanceof MapItem) {
			MapItem m = (MapItem)outer;
			childTerms = new ArrayList<Term>();
			childTerms.add(m.getKey());
			childTerms.add(m.getValue());
		} else if (outer instanceof CollectionItem || outer instanceof Cell || outer instanceof KInjectedLabel || outer instanceof Freezer) {
			return EnumSet.allOf(Fixity.class);
		} else if (outer instanceof KApp) {
			KApp kapp = (KApp) outer;
			childTerms = new ArrayList<Term>();
			childTerms.add(kapp.getLabel());
			childTerms.add(kapp.getChild());
		} else {
			throw new UnsupportedOperationException("position fixity");
		}
		if (childTerms.get(0) == inner)
			set.add(Fixity.BARE_LEFT);
		if (childTerms.get(childTerms.size() - 1) == inner)
			set.add(Fixity.BARE_RIGHT);
		return set;
	}

	/** compute fixity of nonterminal within production */
	private EnumSet<Fixity> getFixity(Term inner, Term outer) {
		if (outer instanceof TermCons) {
			TermCons tc = (TermCons)outer;
			int i;
			for (i = 0; i < tc.getContents().size(); i++) {
				if (inner == tc.getContents().get(i))
					break;
			}
			Production p = tc.getProduction();
			EnumSet<Fixity> set = EnumSet.noneOf(Fixity.class);
			if (!p.hasTerminalToRight(i)) {
				set.add(Fixity.BARE_RIGHT);
			}
			if (!p.hasTerminalToLeft(i)) {
				set.add(Fixity.BARE_LEFT);
			}
			return set;
		} else if (outer instanceof List || outer instanceof Set || outer instanceof Map || outer instanceof Bag) {
			return EnumSet.allOf(Fixity.class);
		} else if (outer instanceof Collection) {
			//KList or KSequence
			Collection c = (Collection) outer;
			int i;
			for (i = 0; i < c.getContents().size(); i++) {
				if (inner == c.getContents().get(i))
					break;
			}
			EnumSet<Fixity> set = EnumSet.allOf(Fixity.class);
			if (i != 0)
				set.remove(Fixity.BARE_LEFT);
			if (i != c.getContents().size())
				set.remove(Fixity.BARE_RIGHT);
			return set;
		} else if (outer instanceof MapItem) {
			MapItem m = (MapItem) outer;
			if (inner == m.getKey())
				return EnumSet.of(Fixity.BARE_LEFT);
			return EnumSet.of(Fixity.BARE_RIGHT);
		} else if (outer instanceof CollectionItem) {
			return EnumSet.noneOf(Fixity.class);
		} else if (outer instanceof Cell) {
			return EnumSet.noneOf(Fixity.class);
		} else if (outer instanceof KApp) {
			KApp kapp = (KApp) outer;
			if (inner == kapp.getLabel())
				return EnumSet.of(Fixity.BARE_LEFT);
			return EnumSet.noneOf(Fixity.class);
		} else if (outer instanceof Freezer) {
			return EnumSet.allOf(Fixity.class);
		} else if (outer instanceof KInjectedLabel) {
			return EnumSet.of(Fixity.BARE_RIGHT);
		}
		throw new UnsupportedOperationException("subterm fixity");
	}

	private boolean isPriorityWrong(Term outer, Term inner) {
		if (outer instanceof TermCons) {
			TermCons tcOuter = (TermCons) outer;
			for (int i = 0; i < tcOuter.getContents().size(); i++) {
				if (DefinitionHelper.isSubsortedEq(tcOuter.getProduction().getChildSort(i), inner.getSort())) {
					return inner instanceof TermCons && DefinitionHelper.isPriorityWrong(tcOuter.getProduction().getKLabel(), ((TermCons)inner).getProduction().getKLabel());
				}
			}
			return !inner.getSort().equals("K");
		} else if (inner instanceof Rewrite && !(outer instanceof Cell)) {
			return true;
		} else if (inner instanceof KSequence && outer instanceof TermCons) {
			return true;
		} else if (outer instanceof KInjectedLabel) {
			KInjectedLabel lbl = (KInjectedLabel)outer;
			String sort = lbl.getTerm().getSort();
			if (MetaK.isKSort(sort)) {
				sort = lbl.getInjectedSort(sort);
				if (!DefinitionHelper.isSubsortedEq(sort, inner.getSort())) {
					return true;
				}
			}
		}
		return false;
	}

	private Stack<ASTNode> stack = new Stack<ASTNode>();

	private void prepare(ASTNode ast) {
		stack.push(ast);
	}

	private boolean postpare() {
		ASTNode inner = stack.pop();
		if (!stack.empty()) {
			ASTNode outer = stack.peek();
			if (outer instanceof Term && inner instanceof Term) {
				if (needsParentheses((Term)inner, (Term)outer)) {
					return true;
				}
			}
		}
		
		return false;
	}

	private boolean getImplicitPriority(Term inner, Term outer) {
		if (getFixity(inner).size() > 0 && getFixity(outer).size() == 0)
			return true;
		if (getFixity(inner).size() > 0 && isUnary(inner) && getFixity(outer).size() > 0 && !isUnary(outer))
			return true;
		return false;
	}

	private boolean needsParentheses(Term inner, Term outer) {
		try {
			boolean priority = isPriorityWrong(outer, inner);
			boolean inversePriority = isPriorityWrong(inner, outer);
			Associativity assoc = getAssociativity(outer);
			if (priority) {
				return true;
			}
			if (isAtom(inner))
				return false;
			if (inversePriority)
				return false;
			EnumSet<Fixity> fixity = getFixity(inner, outer);
			EnumSet<Fixity> position = getPosition(inner, outer);
			boolean implicitPriority = getImplicitPriority(inner, outer);
			boolean implicitInversePriority = getImplicitPriority(outer, inner);
			if (fixity.size() > 0) {
				// implement generic check
				if (assoc == Associativity.NONASSOC && !implicitInversePriority) {
					return true;
				} else if (assoc == Associativity.NONE && implicitPriority) {
					return true;
				}
			}
			if (fixity.contains(Fixity.BARE_LEFT) && assoc == Associativity.RIGHT) {
				// implement lhs check
				if (implicitPriority) {
					return true;
				} else if (!implicitInversePriority && !position.contains(Fixity.BARE_RIGHT)) {
					return true;
				}
			}
			if (fixity.contains(Fixity.BARE_RIGHT) && assoc == Associativity.LEFT) {
				// implement rhs check
				if (implicitPriority) {
					return true;
				} else if (!implicitInversePriority && !position.contains(Fixity.BARE_LEFT)) {
					return true;
				}
			}
			return false;
		} catch (UnsupportedOperationException e) {
			return true;
		}
	}
}
