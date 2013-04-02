package org.kframework.kil.visitors;

import java.util.ArrayList;

import org.kframework.kil.*;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Default implementations of methods visit non-attribute children, and then call the transform method for the parent class on the current node.
 */
public class BasicTransformer implements Transformer {

	private String name;

	public BasicTransformer(String name) {
		this.name = name;
	}

	@Override
	public ASTNode transform(ASTNode node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		for (int i = 0; i < node.getItems().size(); i++) {
			node.getItems().set(i, (DefinitionItem) node.getItems().get(i).accept(this));
		}
		return transform((ASTNode) node);
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
		for (int i = 0; i < node.getItems().size(); i++) {
			node.getItems().set(i, (ModuleItem) node.getItems().get(i).accept(this));
		}
		return transform((DefinitionItem) node);
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
		node.setSort((Sort) node.getSort().accept(this));
		for (int i = 0; i < node.getPriorityBlocks().size(); i++) {
			node.getPriorityBlocks().set(i, (PriorityBlock) node.getPriorityBlocks().get(i).accept(this));
		}
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(PriorityExtended node) throws TransformerException {
		for (int i = 0; i < node.getPriorityBlocks().size(); i++) {
			node.getPriorityBlocks().set(i, (PriorityBlockExtended) node.getPriorityBlocks().get(i).accept(this));
		}
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(PriorityExtendedAssoc node) throws TransformerException {
		for (int i = 0; i < node.getTags().size(); i++) {
			node.getTags().set(i, (Constant) node.getTags().get(i).accept(this));
		}
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(PriorityBlock node) throws TransformerException {
		for (int i = 0; i < node.getProductions().size(); i++) {
			node.getProductions().set(i, (Production) node.getProductions().get(i).accept(this));
		}
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(PriorityBlockExtended node) throws TransformerException {
		for (int i = 0; i < node.getProductions().size(); i++) {
			node.getProductions().set(i, (Constant) node.getProductions().get(i).accept(this));
		}
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Production node) throws TransformerException {
		for (int i = 0; i < node.getItems().size(); i++) {
			node.getItems().set(i, (ProductionItem) node.getItems().get(i).accept(this));
		}
		return transform((ASTNode) node);
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
	public ASTNode transform(Lexical node) throws TransformerException {
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
		for (int i = 0; i < node.getContents().size(); i++) {
			node.getContents().set(i, (Term) node.getContents().get(i).accept(this));
		}
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
			} catch (TransformerException e) {
				exception = e;
			}
		}
		if (terms.isEmpty())
			throw exception;
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
	public ASTNode transform(KList node) throws TransformerException {
		KList result = new KList(node);
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
	public ASTNode transform(ListTerminator node) throws TransformerException {
		return transform((Empty) node);
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
		for (int i = 0; i < node.getContents().size(); i++) {
			node.getContents().set(i, (Term) node.getContents().get(i).accept(this));
		}
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Bracket node) throws TransformerException {
		node.setContent((Term) node.getContent().accept(this));
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Cast node) throws TransformerException {
		node.setContent((Term) node.getContent().accept(this));
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Freezer node) throws TransformerException {
		Term term = (Term) node.getTerm().accept(this);
		Freezer result = new Freezer(node);
		result.setTerm(term);
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(FreezerVariable node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(FreezerSubstitution node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(BackendTerm term) throws TransformerException {
		return transform((Term) term);
	}

	@Override
	public ASTNode transform(Attributes node) throws TransformerException {
		for (int i = 0; i < node.getContents().size(); i++) {
			node.getContents().set(i, (Attribute) node.getContents().get(i).accept(this));
		}
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

	@Override
	public ASTNode transform(KInjectedLabel node) throws TransformerException {
		Term term = (Term) node.getTerm().accept(this);
		KInjectedLabel result = new KInjectedLabel(node);
		result.setTerm(term);
		return transform((Term) result);
	}

    @Override
    public ASTNode transform(FreezerHole node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
	public ASTNode transform(FreezerLabel node) throws TransformerException {
		Term term = (Term) node.getTerm().accept(this);
		FreezerLabel result = new FreezerLabel(node);
		result.setTerm(term);
		return transform((Term) result);
	}

	@Override
	public ASTNode transform(StringSentence node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Restrictions node) throws TransformerException {
		return node;
	}
}
