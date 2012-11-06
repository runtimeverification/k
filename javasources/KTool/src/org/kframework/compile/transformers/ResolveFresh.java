package org.kframework.compile.transformers;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Definition;
import org.kframework.kil.KApp;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


public class ResolveFresh extends CopyOnWriteTransformer {

	private boolean isFresh;
	private Set<Variable> vars = new HashSet<Variable>();

	public ResolveFresh() {
		super("Resolve fresh variables condition.");
	}
	
	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		isFresh = false;
		ASTNode defNode =  super.transform(node);
		if (!isFresh) return node;
		node = (Definition) defNode;
		Configuration cfg = MetaK.getConfiguration(node);
		Bag bag;
		if (cfg.getBody() instanceof Bag) {
			bag = (Bag) cfg.getBody().shallowCopy();
		} else {
			bag = new Bag();
			bag.getContents().add(cfg.getBody());
		}
		cfg.setBody(bag);
		Cell nId = new Cell();
		nId.setLabel("freshCounter");
		nId.setEllipses(Ellipses.NONE);
		Constant zero = new Constant("Int", "0");
		nId.setContents(zero);
		bag.getContents().add(nId);

		return node;
	}

	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		if (null == node.getCondition())
			return node;

		vars.clear();
		ASTNode condNode = node.getCondition().accept(this);
		if (vars.isEmpty())
			return node;

		node = node.shallowCopy();
		node.setCondition((Term) condNode);
		Variable freshVar = MetaK.getFreshVar("Int"); 
		ASTNode bodyNode = node.getBody().accept(new Substitution(createFreshSubstitution(vars, freshVar)));
		assert(bodyNode instanceof Term);
		Bag bag;
		if (bodyNode instanceof Bag) {
			bag = (Bag) bodyNode;
		} else {
			bag = new Bag();
			bag.getContents().add((Term)bodyNode);
		}
		node.setBody(bag);
		
		Cell fCell = new Cell();
		fCell.setLabel("freshCounter");
		fCell.setEllipses(Ellipses.NONE);
		TermCons t = new TermCons("Int", "Int1PlusSyn");
		t.getContents().add(freshVar);
		t.getContents().add(new Constant("Int", Integer.toString(vars.size())));
		fCell.setContents(new Rewrite(freshVar, t));
		bag.getContents().add(fCell);
		
		return node;
	}
	
	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		if ("Bool1FreshSyn".equals(node.getCons())) {
			assert(1 == node.getContents().size());
			assert(node.getContents().get(0) instanceof Variable);

			Variable var = (Variable)node.getContents().get(0);
			this.vars.add(var);
			this.isFresh = true;
			return new Constant("Bool", "true");
		}

		return super.transform(node);
	}

	private static Map<Term, Term> createFreshSubstitution(
			Set<Variable> vars,
			Variable idxVar) {
		Map<Term, Term> result = new HashMap<Term, Term>();
		int idx = 0;
		for (Variable var : vars) {
			TermCons idxTerm = new TermCons("Int", "Int1PlusSyn");
			List<Term> subterms = idxTerm.getContents();
			subterms.add(idxVar);
			subterms.add(new Constant("Int", Integer.toString(idx)));
			++idx;

			String sort = var.getSort();
			String ctor = AddSymbolicSorts.getDefaultSymbolicConstructor(sort);
			Term freshTerm = new KApp(new Constant("KLabel", ctor), idxTerm);
			//TermCons fTerm = new TermCons(var.getSort(), var.getSort() + "1FreshSyn");
			//fTerm.getContents().add(t);
			//result.put(var, fTerm);
			result.put(var, freshTerm);
		}

		return result;
	}

}

