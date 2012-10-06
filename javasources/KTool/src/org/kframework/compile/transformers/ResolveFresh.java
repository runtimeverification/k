package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sentence;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;


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
		production.getAttributes().getContents().add(new Attribute("kgeneratedlabel", "sym" + sort));
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
