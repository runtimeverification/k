package org.kframework.kil.visitors;

import java.util.HashSet;

import org.kframework.kil.*;

public class BasicVisitor implements Visitor {
	protected org.kframework.kil.loader.Context context;
	String name;
	protected HashSet<Integer> visited = null;

	protected void markAsVisited(ASTNode node) {
		if (visited == null) {
			visited = new HashSet<Integer>();
		}
		visited.add(System.identityHashCode(node));
	}

	protected boolean isVisited(ASTNode node) {
		return visited != null && visited.contains(System.identityHashCode(node));
	}

	public BasicVisitor(org.kframework.kil.loader.Context context) {
		this.name = this.getClass().toString();
		this.context = context;
	}

	public BasicVisitor(String name, org.kframework.kil.loader.Context context) {
		this.name = name;
		this.context = context;
	}

	@Override
	public void visit(ASTNode node) {
		if (isVisited(node))
			return;
		markAsVisited(node);
	}

	@Override
	public void visit(ParseError node) {
		if (isVisited(node))
			return;
		visit((ASTNode) node);
	}

	@Override
	public void visit(Definition node) {
		if (isVisited(node))
			return;
		for (DefinitionItem di : node.getItems()) {
			di.accept(this);
		}
		visit((ASTNode) node);
	}

	@Override
	public void visit(DefinitionItem node) {
		if (isVisited(node))
			return;
		visit((ASTNode) node);
	}

	@Override
	public void visit(LiterateDefinitionComment node) {
		if (isVisited(node))
			return;
		visit((DefinitionItem) node);
	}

	@Override
	public void visit(Module node) {
		if (isVisited(node))
			return;
		for (ModuleItem mi : node.getItems()) {
			mi.accept(this);
		}
		visit((DefinitionItem) node);
	}

	@Override
	public void visit(Require require) {
		if (isVisited(require))
			return;
		visit((DefinitionItem) require);
	}

	@Override
	public void visit(ModuleItem node) {
		if (isVisited(node))
			return;
		visit((ASTNode) node);
	}

	@Override
	public void visit(Import node) {
		if (isVisited(node))
			return;
		visit((ModuleItem) node);
	}

	@Override
	public void visit(LiterateModuleComment node) {
		if (isVisited(node))
			return;
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Sentence node) {
		if (isVisited(node))
			return;
		node.getBody().accept(this);
		Term requires = node.getRequires();
		if (requires != null)
			requires.accept(this);
		Term ensures = node.getEnsures();
		if (ensures != null)
			ensures.accept(this);
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Configuration node) {
		if (isVisited(node))
			return;
		visit((Sentence) node);
	}

	@Override
	public void visit(org.kframework.kil.Context node) {
		if (isVisited(node))
			return;
		visit((Sentence) node);
	}

	@Override
	public void visit(Rule node) {
		if (isVisited(node))
			return;
		visit((Sentence) node);
	}

	@Override
	public void visit(Syntax node) {
		if (isVisited(node))
			return;
		node.getSort().accept(this);
		for (PriorityBlock pb : node.getPriorityBlocks()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);
	}

	@Override
	public void visit(PriorityExtended node) {
		if (isVisited(node))
			return;
		for (PriorityBlockExtended pb : node.getPriorityBlocks()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);
	}

	@Override
	public void visit(PriorityExtendedAssoc node) {
		if (isVisited(node))
			return;
		for (KLabelConstant pb : node.getTags()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);
	}

	@Override
	public void visit(PriorityBlock node) {
		if (isVisited(node))
			return;
		for (Production p : node.getProductions()) {
			p.accept(this);
		}
		visit((ASTNode) node);
	}

	@Override
	public void visit(PriorityBlockExtended node) {
		if (isVisited(node))
			return;
		for (Term p : node.getProductions()) {
			p.accept(this);
		}
		visit((ASTNode) node);
	}

	@Override
	public void visit(Production node) {
		if (isVisited(node))
			return;
		for (ProductionItem pi : node.getItems()) {
			pi.accept(this);
		}
		visit((ASTNode) node);
	}

	@Override
	public void visit(ProductionItem node) {
		if (isVisited(node))
			return;
		visit((ASTNode) node);
	}

	@Override
	public void visit(Sort node) {
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
	}

	@Override
	public void visit(Terminal node) {
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
	}

	@Override
	public void visit(Lexical node) {
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
	}

	@Override
	public void visit(UserList node) {
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
	}

	@Override
	public void visit(Term node) {
		if (isVisited(node))
			return;
		visit((ASTNode) node);
	}

	@Override
	public void visit(TermComment node) {
		if (isVisited(node))
			return;
		visit((ASTNode) node);
	}

	@Override
	public void visit(Cell node) {
		if (isVisited(node))
			return;
		node.getContents().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(Collection node) {
		if (isVisited(node))
			return;
		for (Term t : node.getContents()) {
			t.accept(this);
		}
		visit((Term) node);
	}

	@Override
	public void visit(Ambiguity node) {
		if (isVisited(node))
			return;
		visit((Collection) node);
	}

	@Override
	public void visit(Bag node) {
		if (isVisited(node))
			return;
		visit((Collection) node);
	}

	@Override
	public void visit(KSequence node) {
		if (isVisited(node))
			return;
		visit((Collection) node);
	}

	@Override
	public void visit(List node) {
		if (isVisited(node))
			return;
		visit((Collection) node);
	}

	@Override
	public void visit(KList node) {
		if (isVisited(node))
			return;
		visit((Collection) node);
	}

	@Override
	public void visit(Map node) {
		if (isVisited(node))
			return;
		visit((Collection) node);
	}

	@Override
	public void visit(Set node) {
		if (isVisited(node))
			return;
		visit((Collection) node);
	}

	@Override
	public void visit(CollectionItem node) {
		if (isVisited(node))
			return;
		node.getItem().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(BagItem node) {
		if (isVisited(node))
			return;
		visit((CollectionItem) node);
	}

	@Override
	public void visit(ListItem node) {
		if (isVisited(node))
			return;
		visit((CollectionItem) node);
	}

	@Override
	public void visit(MapItem node) {
		if (isVisited(node))
			return;
		node.getKey().accept(this);
		visit((CollectionItem) node);
	}

	@Override
	public void visit(SetItem node) {
		if (isVisited(node))
			return;
		visit((CollectionItem) node);
	}

	@Override
	public void visit(DataStructureBuiltin node) {
		if (isVisited(node))
			return;
		for (Term term : node.baseTerms()) {
			term.accept(this);
		}

		visit((Term) node);
	}

	@Override
	public void visit(CollectionBuiltin node) {
		if (isVisited(node))
			return;
		for (Term term : node.elements()) {
			term.accept(this);
		}

		visit((DataStructureBuiltin) node);
	}

    @Override
    public void visit(SetBuiltin node) {
		if (isVisited(node))
			return;
		for (Term entry : node.elements()) {
			entry.accept(this);
		}

		visit((DataStructureBuiltin) node);
    }

    @Override
    public void visit(SetLookup node) {
		if (isVisited(node))
			return;
		node.base().accept(this);
		node.key().accept(this);
		visit((Term) node);
    }

    @Override
    public void visit(SetUpdate node) {
		if (isVisited(node))
			return;
		node.set().accept(this);
		for (Term entry : node.removeEntries()) {
			entry.accept(this);
		}
		visit((Term) node);
    }

    @Override
	public void visit(ListBuiltin node) {
		if (isVisited(node))
			return;
		for (Term entry : node.elementsLeft()) {
			entry.accept(this);
		}
		for (Term entry : node.elementsRight()) {
			entry.accept(this);
		}

		visit((DataStructureBuiltin) node);
	}

	@Override
	public void visit(ListLookup node) {
		if (isVisited(node))
			return;
		node.base().accept(this);
		node.key().accept(this);
		node.value().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(ListUpdate node) {
		if (isVisited(node))
			return;
		node.base().accept(this);
		for (Term entry : node.removeLeft()) {
			entry.accept(this);
		}
        for (Term entry : node.removeRight()) {
			entry.accept(this);
		}
		visit((Term) node);
	}

    @Override
	public void visit(MapBuiltin node) {
		if (isVisited(node))
			return;
		for (java.util.Map.Entry<Term, Term> entry : node.elements().entrySet()) {
			entry.getKey().accept(this);
			entry.getValue().accept(this);
		}

		visit((DataStructureBuiltin) node);
	}

	@Override
	public void visit(MapLookup node) {
		if (isVisited(node))
			return;
		node.base().accept(this);
		node.key().accept(this);
		node.value().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(MapUpdate node) {
		if (isVisited(node))
			return;
		node.map().accept(this);
		for (java.util.Map.Entry<Term, Term> entry : node.removeEntries().entrySet()) {
			entry.getKey().accept(this);
			entry.getValue().accept(this);
		}
		for (java.util.Map.Entry<Term, Term> entry : node.updateEntries().entrySet()) {
			entry.getKey().accept(this);
			entry.getValue().accept(this);
		}
		visit((Term) node);
	}

	@Override
	public void visit(Token node) {
		if (isVisited(node))
			return;
		visit((KLabel) node);
	}

	@Override
	public void visit(BoolBuiltin node) {
		if (isVisited(node))
			return;
		visit((Token) node);
	}

	@Override
	public void visit(IntBuiltin node) {
		if (isVisited(node))
			return;
		visit((Token) node);
	}

	@Override
	public void visit(StringBuiltin node) {
		if (isVisited(node))
			return;
		visit((Token) node);
	}

	@Override
	public void visit(GenericToken node) {
		if (isVisited(node))
			return;
		visit((Token) node);
	}

	@Override
	public void visit(Empty node) {
		if (isVisited(node))
			return;
		visit((Term) node);
	}

	@Override
	public void visit(ListTerminator node) {
		if (isVisited(node))
			return;
		visit((Empty) node);
	}

	@Override
	public void visit(Hole node) {
		if (isVisited(node))
			return;
		visit((Term) node);
	}

	@Override
	public void visit(FreezerHole node) {
		if (isVisited(node))
			return;
		visit((Term) node);
	}

	@Override
	public void visit(KApp node) {
		if (isVisited(node))
			return;
		node.getLabel().accept(this);
		node.getChild().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(KLabel node) {
		if (isVisited(node))
			return;
		visit((Term) node);
	}

	@Override
	public void visit(KLabelConstant node) {
		if (isVisited(node))
			return;
		visit((KLabel) node);
	}

	@Override
	public void visit(Rewrite node) {
		if (isVisited(node))
			return;
		node.getLeft().accept(this);
		node.getRight().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(TermCons node) {
		if (isVisited(node))
			return;
		for (Term t : node.getContents()) {
			t.accept(this);
		}
		visit((Term) node);
	}

	@Override
	public void visit(Bracket node) {
		if (isVisited(node))
			return;
		node.getContent().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(Cast node) {
		if (isVisited(node))
			return;
		node.getContent().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(Variable node) {
		if (isVisited(node))
			return;
		visit((Term) node);
	}

	public void visit(Attributes attributes) {
		if (isVisited(attributes))
			return;
		for (Attribute t : attributes.getContents()) {
			t.accept(this);
		}
		visit((ASTNode) attributes);
	}

	@Override
	public void visit(Attribute attribute) {
		if (isVisited(attribute))
			return;
		visit((ASTNode) attribute);
	}

	@Override
	public void visit(StringSentence node) {
		if (isVisited(node))
			return;
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Restrictions node) {
		if (isVisited(node))
			return;
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Freezer f) {
		if (isVisited(f))
			return;
		f.getTerm().accept(this);
		visit((Term) f);
	}

	@Override
	public void visit(BackendTerm term) {
		if (isVisited(term))
			return;
		visit((Term) term);
	}

	@Override
	public void visit(KInjectedLabel kInjectedLabel) {
		if (isVisited(kInjectedLabel))
			return;
		kInjectedLabel.getTerm().accept(this);
		visit((Term) kInjectedLabel);
	}

	@Override
	public void visit(FreezerLabel freezerLabel) {
		if (isVisited(freezerLabel))
			return;
		freezerLabel.getTerm().accept(this);
		visit((Term) freezerLabel);
	}

	@Override
	public String getName() {
		return name;
	}
}
