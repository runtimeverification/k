package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bracket;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.List;

public class TypeCheckFilter extends CopyOnWriteTransformer {

	private int score = 0;
	private TermCons parentTermCons = null;
	private int parentTermConsIndex = -1;
	public TypeCheckFilter() {
		super("Type check filter");
	}

	@Override
	public ASTNode transform(Ambiguity amb) throws TransformerException {
		List<Term> results = new ArrayList<Term>();
		List<Integer> scores = new ArrayList<Integer>();
		for (Term choice : amb.getContents()) {
			choice = choice.shallowCopy();
			int currentScore = score;
			Term result = acceptChild(choice, parentTermCons, parentTermConsIndex);
			results.add(result);	
			scores.add(score);
			score = currentScore;
		}

		int maxScore = scores.get(0);
		for(int chosenScore : scores) {
			if (chosenScore > maxScore) {
				maxScore = chosenScore;
			}
		}

		List<Term> terms = new ArrayList<Term>();
		for (int j = 0; j < scores.size(); j++) {
			if (scores.get(j) == maxScore) {
				terms.add(results.get(j));
			}
		}

		//score = maxScore;
		if (terms.size() == 1) {
			return terms.get(0);
		} else {
			amb.setContents(terms);
			return amb;
		}
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		for(int i = 0; i < tc.getContents().size(); i++) {
			Term child = tc.getContents().get(i);
			if (child instanceof Ambiguity) {
				parentTermCons = tc;
				parentTermConsIndex = i;
				tc.getContents().set(i, (Term)child.accept(this));
				parentTermCons = null;
				parentTermConsIndex = -1;
			} else {
				tc.getContents().set(i, acceptChild(child, tc,  i));
			}
		}

		return tc;
	}

	private Term acceptChild(Term child, TermCons parent, int idx) throws TransformerException {
		if (child instanceof Rewrite) {
			Rewrite rw = (Rewrite) child;
			Term left = acceptChild(rw.getLeft(), parent, idx);
			Term right = acceptChild(rw.getRight(), parent, idx);
			rw.setLeft(left);
			rw.setRight(right);
			return rw;
		} else if (child instanceof Bracket) {
			Bracket br = (Bracket) child;
			return acceptChild(br.getContent(), parent, idx);
		}
		if (parent == null) 
			return (Term)child.accept(this);
		
		String sort = parent.getProduction().getChildSort(idx);
		if (!DefinitionHelper.isSubsortedEq(sort, child.getSort()) && !(DefinitionHelper.isSubsortedEq("K", child.getSort()) && (child.getSort().equals("K") || sort.equals("K")))) {
			score -= 1;
		}
		return (Term)child.accept(this);
	}
}
