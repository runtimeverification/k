package ro.uaic.info.fmse.visitors;

import java.util.ArrayList;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Ambiguity;
import ro.uaic.info.fmse.k.Attribute;
import ro.uaic.info.fmse.k.Attributes;
import ro.uaic.info.fmse.k.Bag;
import ro.uaic.info.fmse.k.BagItem;
import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.k.Collection;
import ro.uaic.info.fmse.k.CollectionItem;
import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.Context;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.DefinitionItem;
import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.Hole;
import ro.uaic.info.fmse.k.Import;
import ro.uaic.info.fmse.k.KApp;
import ro.uaic.info.fmse.k.KLabel;
import ro.uaic.info.fmse.k.KSequence;
import ro.uaic.info.fmse.k.List;
import ro.uaic.info.fmse.k.ListItem;
import ro.uaic.info.fmse.k.ListOfK;
import ro.uaic.info.fmse.k.LiterateDefinitionComment;
import ro.uaic.info.fmse.k.LiterateModuleComment;
import ro.uaic.info.fmse.k.Map;
import ro.uaic.info.fmse.k.MapItem;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.ModuleItem;
import ro.uaic.info.fmse.k.PriorityBlock;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.ProductionItem;
import ro.uaic.info.fmse.k.Rewrite;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.k.Sentence;
import ro.uaic.info.fmse.k.Set;
import ro.uaic.info.fmse.k.SetItem;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.Terminal;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.k.Variable;

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
