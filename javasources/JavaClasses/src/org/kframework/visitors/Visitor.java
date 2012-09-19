package org.kframework.visitors;

import org.kframework.k.ASTNode;
import org.kframework.k.Ambiguity;
import org.kframework.k.Attribute;
import org.kframework.k.Attributes;
import org.kframework.k.Bag;
import org.kframework.k.BagItem;
import org.kframework.k.Cell;
import org.kframework.k.Collection;
import org.kframework.k.CollectionItem;
import org.kframework.k.Configuration;
import org.kframework.k.Constant;
import org.kframework.k.Context;
import org.kframework.k.Definition;
import org.kframework.k.DefinitionItem;
import org.kframework.k.Empty;
import org.kframework.k.Hole;
import org.kframework.k.Import;
import org.kframework.k.KApp;
import org.kframework.k.KLabel;
import org.kframework.k.KSequence;
import org.kframework.k.List;
import org.kframework.k.ListItem;
import org.kframework.k.ListOfK;
import org.kframework.k.LiterateDefinitionComment;
import org.kframework.k.LiterateModuleComment;
import org.kframework.k.Map;
import org.kframework.k.MapItem;
import org.kframework.k.Module;
import org.kframework.k.ModuleItem;
import org.kframework.k.PriorityBlock;
import org.kframework.k.Production;
import org.kframework.k.ProductionItem;
import org.kframework.k.Require;
import org.kframework.k.Rewrite;
import org.kframework.k.Rule;
import org.kframework.k.Sentence;
import org.kframework.k.Set;
import org.kframework.k.SetItem;
import org.kframework.k.Sort;
import org.kframework.k.Syntax;
import org.kframework.k.Term;
import org.kframework.k.TermComment;
import org.kframework.k.TermCons;
import org.kframework.k.Terminal;
import org.kframework.k.UserList;
import org.kframework.k.Variable;

public interface Visitor {
	public void visit(ASTNode node);
	public void visit(Definition node);
	public void visit(DefinitionItem node);
	// <DefinitionItems>
	public void visit(LiterateDefinitionComment node);
	public void visit(Module node);
	public void visit(Require require);
	// </DefinitionItems>
	public void visit(ModuleItem node);
	// <ModuleItems>
	public void visit(Import node);
	public void visit(LiterateModuleComment node);
	public void visit(Sentence node);
	// <Sentences>
	public void visit(Configuration node);
	public void visit(Context node);
	public void visit(Rule node);
	// </Sentences>
	public void visit(Syntax node);
	// <ModuleItems>
	public void visit(PriorityBlock node);
	public void visit(Production node);
	public void visit(ProductionItem node);
	// <ProductionItems>
	public void visit(Sort node);
	public void visit(Terminal node);
	public void visit(UserList node);
	// </ProductionItems>
	public void visit(Term node);
	// <Terms>
	public void visit(Cell node);
	public void visit(Collection node);
	// <Collections>
	public void visit(Ambiguity node);
	public void visit(Bag node);
	public void visit(KSequence node);
	public void visit(List node);
	public void visit(ListOfK node);
	public void visit(Map node);
	public void visit(Set node);
	// </Collections>
	public void visit(CollectionItem node);
	// <CollectionItems>
	public void visit(BagItem node);
	public void visit(ListItem node);
	public void visit(MapItem node);
	public void visit(SetItem node);
	// </CollectionItems>
	public void visit(Constant node);
	public void visit(Empty node);
	public void visit(Hole node);
	public void visit(KApp node);
	public void visit(KLabel node);
	public void visit(Rewrite node);
	public void visit(TermCons node);
	public void visit(Variable node);
	// </Terms>
	public void visit(Attributes attributes);
	public void visit(Attribute attribute);
	public void visit(TermComment node);
}
