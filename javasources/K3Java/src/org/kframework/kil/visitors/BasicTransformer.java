package org.kframework.kil.visitors;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Empty;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabel;
import org.kframework.kil.KSequence;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.ListOfK;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.exceptions.TransformerException;


public class BasicTransformer implements Transformer {
	
	private String name;

	public BasicTransformer(String name) {this.name = name;}

	@Override
	public ASTNode transform(ASTNode node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		ArrayList<DefinitionItem> items = new ArrayList<DefinitionItem>();
		for (DefinitionItem di : node.getItems()) {
			items.add((DefinitionItem) di.accept(this));
		}
		Definition result = new Definition(node);
		result.setItems(items);
		return transform((ASTNode) result);
	}

	@Override
	public ASTNode transform(DefinitionItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(LiterateDefinitionComment node) throws TransformerException {
		return transform((DefinitionItem) node);
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		ArrayList<ModuleItem> items = new ArrayList<ModuleItem>();
		for (ModuleItem mi : node.getItems()) {
			items.add((ModuleItem) mi.accept(this));
		}
		Module result = new Module(node);
		result.setItems(items);
		return transform((DefinitionItem) result);
	}

	@Override
	public ASTNode transform(ModuleItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Import node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(LiterateModuleComment node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		Term body = (Term) node.getBody().accept(this);
		Term condition = node.getCondition();
		if (condition != null)
			condition = (Term) condition.accept(this);
		node.setBody(body);
		node.setCondition(condition);
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		Configuration c = new Configuration(node);
		return transform((Sentence) c);
	}

	@Override
	public ASTNode transform(Context node) throws TransformerException {
		Context c = new Context(node);
		return transform((Sentence) c);
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		Rule r = new Rule(node);
		return transform((Sentence) r);
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		ArrayList<PriorityBlock> pbs = new ArrayList<PriorityBlock>();
		for (PriorityBlock pb : node.getPriorityBlocks()) {
			pbs.add((PriorityBlock) pb.accept(this));
		}
		Syntax result = new Syntax(node);
		result.setPriorityBlocks(pbs);
		return transform((ModuleItem) result);
	}

	@Override
	public ASTNode transform(PriorityBlock node) throws TransformerException {
		ArrayList<Production> prods = new ArrayList<Production>();
		for (Production p : node.getProductions()) {
			prods.add((Production) p.accept(this));
		}
		PriorityBlock result = new PriorityBlock(node);
		result.setProductions(prods);
		return transform((ASTNode) result);
	}

	@Override
	public ASTNode transform(Production node) throws TransformerException {
		ArrayList<ProductionItem> pis = new ArrayList<ProductionItem>();
		for (ProductionItem pi : node.getItems()) {
			pis.add((ProductionItem) pi.accept(this));
		}
		Production result = new Production(node);
		result.setItems(pis);
		return transform((ASTNode) result);
	}

	@Override
	public ASTNode transform(ProductionItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Sort node) throws TransformerException {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Terminal node) throws TransformerException {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(UserList node) throws TransformerException {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Term node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		Cell result = new Cell(node);
		result.setContents((Term) node.getContents().accept(this));
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(Collection node) throws TransformerException {
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			terms.add((Term) t.accept(this));
		}
		node.setContents(terms);
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Ambiguity node) throws TransformerException {
		TransformerException exception = null;
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			ASTNode result = null;
			try {
				result = t.accept(this);
				terms.add((Term) result);
			}
			catch (TransformerException e) {
				exception = e;
			}
		}
		if (terms.isEmpty()) throw new TransformerException(exception);
		if (terms.size() == 1) {
			return terms.get(0);
		}
		node.setContents(terms);
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Bag node) throws TransformerException {
		Bag result = new Bag(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(KSequence node) throws TransformerException {
		KSequence result = new KSequence(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(List node) throws TransformerException {
		List result = new List(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(ListOfK node) throws TransformerException {
		ListOfK result = new ListOfK(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(Map node) throws TransformerException {
		Map result = new Map(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(Set node) throws TransformerException {
		Set result = new Set(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(CollectionItem node) throws TransformerException {
		node.setItem((Term) node.getItem().accept(this));
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(BagItem node) throws TransformerException {
		BagItem result = new BagItem(node);
		return transform((CollectionItem) result);
	}

	@Override
	public ASTNode transform(ListItem node) throws TransformerException {
		ListItem result = new ListItem(node);
		return transform((CollectionItem) result);
	}

	@Override
	public ASTNode transform(MapItem node) throws TransformerException {
		MapItem result = new MapItem(node);
		result.setKey((Term) node.getKey().accept(this));
		result.setValue((Term) node.getValue().accept(this));
		return transform((CollectionItem) result);
	}

	@Override
	public ASTNode transform(SetItem node) throws TransformerException {
		SetItem result = new SetItem(node);
		return transform((CollectionItem) result);
	}

	@Override
	public ASTNode transform(Constant node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Empty node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Hole node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(KApp node) throws TransformerException {
		KApp result = new KApp(node);
		result.setLabel((Term) node.getLabel().accept(this));
		result.setChild((Term) node.getChild().accept(this));
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(KLabel node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		Rewrite result = new Rewrite(node);
		result.setLeft((Term) node.getLeft().accept(this));
		result.setRight((Term) node.getRight().accept(this));
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			terms.add((Term) t.accept(this));
		}
		TermCons result = new TermCons(node);
		result.setContents(terms);
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Attributes node) throws TransformerException {
		java.util.List<Attribute> contents = new ArrayList<Attribute>();
		for (Attribute at : node.getContents())
			contents.add((Attribute) at.accept(this));
		node.setContents(contents);
		return node;
	}

	@Override
	public ASTNode transform(Attribute node) throws TransformerException {
		return transform((Attribute) node);
	}

	@Override
	public String getName() {
		return name;
	}
}
