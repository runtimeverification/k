package org.kframework.kil.visitors;

import java.util.HashSet;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionBuiltin;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.DataStructureBuiltin;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Empty;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.FreezerLabel;
import org.kframework.kil.GenericToken;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Lexical;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.Map;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.MapItem;
import org.kframework.kil.MapLookup;
import org.kframework.kil.MapUpdate;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityBlockExtended;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Require;
import org.kframework.kil.Restrictions;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.Token;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;

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
		return;
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
		Term condition = node.getCondition();
		if (condition != null)
			condition.accept(this);
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
		node.map().accept(this);
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
	public void visit(Constant node) {
		if (isVisited(node))
			return;
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
