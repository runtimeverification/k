package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Attribute;
import org.kframework.k.Bag;
import org.kframework.k.Cell;
import org.kframework.k.Configuration;
import org.kframework.k.Constant;
import org.kframework.k.Definition;
import org.kframework.k.Module;
import org.kframework.k.PriorityBlock;
import org.kframework.k.Production;
import org.kframework.k.ProductionItem;
import org.kframework.k.Rewrite;
import org.kframework.k.Sentence;
import org.kframework.k.Sort;
import org.kframework.k.Syntax;
import org.kframework.k.Term;
import org.kframework.k.TermCons;
import org.kframework.k.Terminal;
import org.kframework.k.Variable;
import org.kframework.loader.DefinitionHelper;
import org.kframework.visitors.CopyOnWriteTransformer;


public class ResolveFresh extends CopyOnWriteTransformer {
	boolean isFresh;
	Set<Variable> vars;
	Set<String> sorts = new HashSet<String>();
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
			bag = (Bag) cfg.getBody();
		} else {
			bag = new Bag();
			bag.getContents().add(cfg.getBody());
			cfg.setBody(bag);
		}
		Cell nId = new Cell();
		nId.setLabel("freshCounter");
		nId.setElipses("none");
		Constant zero = new Constant("Int", "0");
		nId.setContents(zero);
		bag.getContents().add(nId);

		return node;
	}
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		sorts = new HashSet<String>();
		ASTNode modNode = super.transform(node);
		if (sorts.isEmpty()) return node;
		node = (Module) modNode;
		for (String sort : sorts) {
			Syntax sDecl = declareFreshWrapper(sort);
			node.getItems().add(sDecl);			
		}
		return node;
	}


	private Syntax declareFreshWrapper(String sort) {
		List<PriorityBlock> pBlocks = new ArrayList<PriorityBlock>();
		PriorityBlock pBlock = new PriorityBlock();
		List<ProductionItem> proditems = new ArrayList<ProductionItem>();
		proditems.add(new Terminal("sym" + sort));
		proditems.add(new Terminal("("));
		proditems.add(new Sort("Int"));
		proditems.add(new Terminal(")"));
		Production production = new Production(new Sort(sort), proditems );
		production.getAttributes().getContents().add(new Attribute("cons", sort + "1FreshSyn"));
		production.getAttributes().getContents().add(new Attribute("prefixlabel", "sym" + sort + "`(_`)"));
		pBlock.getProductions().add(production);
		pBlocks.add(pBlock);
		DefinitionHelper.conses.put(sort + "1FreshSyn", production);
		return new Syntax(new Sort(sort), pBlocks );
	}
	
	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		vars = new HashSet<Variable>();
		if (null == node.getCondition()) return node;
		ASTNode condNode = node.getCondition().accept(this);
		if (vars.isEmpty()) return node;
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
		fCell.setElipses("none");
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
			isFresh = true;
			vars.add(var);
			sorts.add(var.getSort());
			return new Constant("Bool", "true");
		}
		return super.transform(node);
	}

	private Map<Term, Term> createFreshSubstitution(Set<Variable> vars2,
			Variable freshVar) {
		Map<Term, Term> result = new HashMap<Term, Term>();
		int i = 0;
		for (Variable var : vars2) {
			TermCons fTerm = new TermCons(var.getSort(), var.getSort() + "1FreshSyn");
			TermCons t = new TermCons("Int", "Int1PlusSyn");
			t.getContents().add(freshVar);
			t.getContents().add(new Constant("Int", Integer.toString(i)));
			fTerm.getContents().add(t);
			result.put(var, fTerm);
		}
		return result;
	}

}
