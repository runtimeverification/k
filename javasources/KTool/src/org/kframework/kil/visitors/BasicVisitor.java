package org.kframework.kil.visitors;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Empty;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.FreezerLabel;
import org.kframework.kil.FreezerSubstitution;
import org.kframework.kil.FreezerVariable;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabel;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Lexical;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
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
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;

public class BasicVisitor implements Visitor {

	String name;

	public BasicVisitor() {
		this.name = this.getClass().toString();
	}

	public BasicVisitor(String name) {
		this.name = name;
	}

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
	public void visit(Require require) {
		visit((DefinitionItem) require);
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
	public void visit(PriorityExtended node) {
		for (PriorityBlockExtended pb : node.getPriorityBlocks()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);
	}

	@Override
	public void visit(PriorityExtendedAssoc node) {
		for (Constant pb : node.getTags()) {
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
	public void visit(PriorityBlockExtended node) {
		for (Term p : node.getProductions()) {
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
	public void visit(Lexical node) {
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
	public void visit(KList node) {
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
	public void visit(ListTerminator node) {
		visit((Empty) node);
	}

	@Override
	public void visit(Hole node) {
		visit((Term) node);
	}

	@Override
	public void visit(FreezerHole node) {
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
	public void visit(Bracket node) {
		node.getContent().accept(this);
		visit((Term) node);
	}

	@Override
	public void visit(Cast node) {
		node.getContent().accept(this);
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

	@Override
	public void visit(StringSentence node) {
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Restrictions node) {
		visit((ModuleItem) node);
	}

	@Override
	public void visit(Freezer f) {
		f.getTerm().accept(this);
		visit((Term) f);
	}

	@Override
	public void visit(FreezerVariable var) {
		visit((Term) var);
	}

	@Override
	public void visit(FreezerSubstitution subst) {
		visit((Term) subst);
	}

	@Override
	public void visit(BackendTerm term) {
		visit((Term) term);
	}

	@Override
	public void visit(KInjectedLabel kInjectedLabel) {
		kInjectedLabel.getTerm().accept(this);
		visit((Term) kInjectedLabel);
	}

	@Override
	public void visit(FreezerLabel freezerLabel) {
		freezerLabel.getTerm().accept(this);
		visit((Term) freezerLabel);
	}

	@Override
	public String getName() {
		return name;
	}
}
