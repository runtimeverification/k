package org.kframework.kil.visitors;

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
import org.kframework.kil.Require;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;

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
