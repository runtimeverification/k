package ro.uaic.info.fmse.visitors;

import ro.uaic.info.fmse.k.*;

public class BasicVisitor implements Visitor {

	@Override
	public void visit(ASTNode node) {
		return;
	}

	@Override
	public void visit(Definition node) {
		for (DefinitionItem di : node.getItems()) {
			di.accept(this);
		}
		visit((ASTNode) node);
	}

	@Override
	public void visit(DefinitionItem node) {
		visit((ASTNode) node);
	}

	@Override
	public void visit(LiterateDefinitionComment node) {
		visit((DefinitionItem) node);
	}

	@Override
	public void visit(Module node) {
		for (ModuleItem mi : node.getItems()) {
			mi.accept(this);
		}
		visit((DefinitionItem) node);
	}

	@Override
	public void visit(ModuleItem node) {
		visit((ASTNode) node);
	}

	@Override
	public void visit(Import node) {
		visit((ModuleItem) node);
	}

	@Override
	public void visit(LiterateModuleComment node) {
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Sentence node) {
		node.getBody().accept(this);
		Term condition = node.getCondition();
		if (condition != null)
			condition.accept(this);
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Configuration node) {
		visit((Sentence) node);
	}

	@Override
	public void visit(Context node) {
		visit((Sentence) node);
	}

	@Override
	public void visit(Rule node) {
		visit((Sentence) node);
	}

	@Override
	public void visit(Syntax node) {
		node.getSort().accept(this);
		for (PriorityBlock pb : node.getPriorityBlocks()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);
	}

	@Override
	public void visit(PriorityBlock node) {
		for (Production p : node.getProductions()) {
			p.accept(this);
		}
		visit((ASTNode) node);
	}

	@Override
	public void visit(Production node) {
		for (ProductionItem pi : node.getItems()) {
			pi.accept(this);
		}
		visit((ASTNode) node);
	}

	@Override
	public void visit(ProductionItem node) {
		visit((ASTNode) node);
	}

	@Override
	public void visit(Sort node) {
		visit((ProductionItem) node);
	}

	@Override
	public void visit(Terminal node) {
		visit((ProductionItem) node);
	}

	@Override
	public void visit(UserList node) {
		visit((ProductionItem) node);
	}

	@Override
	public void visit(Term node) {
		visit((ASTNode) node);
	}

	@Override
	public void visit(TermComment node) {
		visit((ASTNode) node);
	}

	@Override
	public void visit(Cell node) {
		node.getContents().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(Collection node) {
		for (Term t : node.getContents()) {
			t.accept(this);
		}
		visit((Term) node);
	}

	@Override
	public void visit(Ambiguity node) {
		visit((Collection) node);
	}

	@Override
	public void visit(Bag node) {
		visit((Collection) node);
	}

	@Override
	public void visit(KSequence node) {
		visit((Collection) node);
	}

	@Override
	public void visit(List node) {
		visit((Collection) node);
	}

	@Override
	public void visit(ListOfK node) {
		visit((Collection) node);
	}

	@Override
	public void visit(Map node) {
		visit((Collection) node);
	}

	@Override
	public void visit(Set node) {
		visit((Collection) node);
	}

	@Override
	public void visit(CollectionItem node) {
		node.getItem().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(BagItem node) {
		node.getItem().accept(this);
		visit((CollectionItem) node);
	}

	@Override
	public void visit(ListItem node) {
		visit((CollectionItem) node);
	}

	@Override
	public void visit(MapItem node) {
		node.getKey().accept(this);
		visit((CollectionItem) node);
	}

	@Override
	public void visit(SetItem node) {
		visit((CollectionItem) node);
	}

	@Override
	public void visit(Constant node) {
		visit((Term) node);
	}

	@Override
	public void visit(Empty node) {
		visit((Term) node);
	}

	@Override
	public void visit(Hole node) {
		visit((Term) node);
	}

	@Override
	public void visit(KApp node) {
		node.getLabel().accept(this);
		node.getChild().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(KLabel node) {
		visit((Term) node);
	}

	@Override
	public void visit(Rewrite node) {
		node.getLeft().accept(this);
		node.getRight().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(TermCons node) {
		for (Term t : node.getContents()) {
			t.accept(this);
		}
		visit((Term) node);
	}

	@Override
	public void visit(Variable node) {
		visit((Term) node);
	}

	public void visit(Attributes attributes) {
		for (Attribute t : attributes.getContents()) {
			t.accept(this);
		}
		visit((ASTNode) attributes);
	}

	@Override
	public void visit(Attribute attribute) {
		visit((ASTNode) attribute);
	}
}
