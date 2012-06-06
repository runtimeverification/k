package ro.uaic.info.fmse.visitors;

import java.util.ArrayList;
import ro.uaic.info.fmse.k.*;

public class BasicTransformer implements Transformer {

	@Override
	public ASTNode transform(ASTNode node) {
		return node;
	}

	@Override
	public ASTNode transform(Definition node) {
		ArrayList<DefinitionItem> items = new ArrayList<DefinitionItem>();
		for (DefinitionItem di : node.getItems()) {
			items.add((DefinitionItem)di.accept(this));
		}
		Definition result = new Definition(node);
		result.setItems(items);
		return transform((ASTNode) result);
	}

	@Override
	public ASTNode transform(DefinitionItem node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(LiterateDefinitionComment node) {
		return transform((DefinitionItem) node);
	}

	@Override
	public ASTNode transform(Module node) {
		ArrayList<ModuleItem> items = new ArrayList<ModuleItem>();
		for (ModuleItem mi : node.getItems()) {
			items.add((ModuleItem) mi.accept(this));
		}
		Module result = new Module(node);
		result.setItems(items);
		return transform((DefinitionItem) result);
	}

	@Override
	public ASTNode transform(ModuleItem node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Import node) {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(LiterateModuleComment node) {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Sentence node) {
		Term body = (Term) node.getBody().accept(this);
		Term condition = node.getCondition();
		if (condition != null)
			condition = (Term) condition.accept(this);
		node.setBody(body);
		node.setCondition(condition);
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Configuration node) {
		Configuration c = new Configuration(node);
		return transform((Sentence)c);
	}

	@Override
	public ASTNode transform(Context node) {
		Context c = new Context(node);
		return transform((Sentence)c);
	}

	@Override
	public ASTNode transform(Rule node) {
		Rule r = new Rule(node);
		return transform((Sentence)r);
	}

	@Override
	public ASTNode transform(Syntax node) {
		ArrayList<PriorityBlock> pbs = new ArrayList<PriorityBlock>();
		for (PriorityBlock pb : node.getPriorityBlocks()) {
			pbs.add((PriorityBlock)pb.accept(this));
		}
		Syntax result = new Syntax(node);
		result.setPriorityBlocks(pbs);
		return transform((ModuleItem) result);
	}

	@Override
	public ASTNode transform(PriorityBlock node) {
		ArrayList<Production> prods = new ArrayList<Production>();
		for (Production p : node.getProductions()) {
			prods.add((Production) p.accept(this));
		}
		PriorityBlock result = new PriorityBlock(node);
		result.setProductions(prods);
		return transform((ASTNode) result);
	}

	@Override
	public ASTNode transform(Production node) {
		ArrayList<ProductionItem> pis = new ArrayList<ProductionItem>();
		for (ProductionItem pi : node.getItems()) {
			pis.add((ProductionItem)pi.accept(this));
		}
		Production result = new Production(node);
		result.setItems(pis);
		return transform((ASTNode) result);
	}

	@Override
	public ASTNode transform(ProductionItem node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Sort node) {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Terminal node) {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(UserList node) {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Term node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Cell node) {
		Cell result = new Cell(node);
		result.setContents((Term) node.getContents().accept(this));
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(Collection node) {
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			terms.add((Term)t.accept(this));
		}
		node.setContents(terms);
		return transform((Term) node);
	}
	
	@Override
	public ASTNode transform(Ambiguity node) {
		Ambiguity result = new Ambiguity(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(Bag node) {
		Bag result = new Bag(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(K node) {
		K result = new K(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(KSequence node) {
		KSequence result = new KSequence(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(List node) {
		List result = new List(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(ListOfK node) {
		ListOfK result = new ListOfK(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(Map node) {
		Map result = new Map(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(Set node) {
		Set result = new Set(node);
		return transform((Collection) result);
	}

	@Override
	public ASTNode transform(CollectionItem node) {
		node.setItem((Term) node.getItem().accept(this));
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(BagItem node) {
		BagItem result = new BagItem(node);
		return transform((CollectionItem) result);
	}
	@Override
	public ASTNode transform(ListItem node) {
		ListItem result = new ListItem(node);
		return transform((CollectionItem) result);
	}

	@Override
	public ASTNode transform(MapItem node) {
		MapItem result = new MapItem(node);
		result.setKey((Term) node.getKey().accept(this));
		return transform((CollectionItem) result);
	}

	@Override
	public ASTNode transform(SetItem node) {
		SetItem result = new SetItem(node);
		return transform((CollectionItem) result);
	}	
	
	@Override
	public ASTNode transform(Constant node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Empty node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Hole node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(KApp node) {
		KApp result = new KApp(node);
		result.setLabel((Term) node.getLabel().accept(this));
		result.setChild((Term) node.getChild().accept(this));
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(KLabel node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Rewrite node) {
		Rewrite result = new Rewrite(node);
		result.setLeft((Term) node.getLeft().accept(this));
		result.setRight((Term) node.getRight().accept(this));
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(TermCons node) {
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			terms.add((Term) t.accept(this));
		}
		TermCons result = new TermCons(node);
		result.setContents(terms);
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(Variable node) {
		return transform((Term) node);
	}

}
