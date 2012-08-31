package ro.uaic.info.fmse.visitors;

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
import ro.uaic.info.fmse.k.TermComment;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.Terminal;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.k.Require;

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
