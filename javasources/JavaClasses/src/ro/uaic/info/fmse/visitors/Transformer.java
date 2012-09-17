package ro.uaic.info.fmse.visitors;

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

public interface Transformer {
	public ASTNode transform(ASTNode node) throws TransformerException;
	public ASTNode transform(Definition node) throws TransformerException;
	public ASTNode transform(DefinitionItem node) throws TransformerException;
	//<DefinitionItems>
	public ASTNode transform(LiterateDefinitionComment node) throws TransformerException;
	public ASTNode transform(Module node) throws TransformerException;
	//</DefinitionItems>    
	public ASTNode transform(ModuleItem node) throws TransformerException;
	//<ModuleItems>
	public ASTNode transform(Import node) throws TransformerException;
	public ASTNode transform(LiterateModuleComment node) throws TransformerException;
	public ASTNode transform(Sentence node) throws TransformerException;
	//	<Sentences>
	public ASTNode transform(Configuration node) throws TransformerException;
	public ASTNode transform(Context node) throws TransformerException;
	public ASTNode transform(Rule node) throws TransformerException;
	//	</Sentences>
	public ASTNode transform(Syntax node) throws TransformerException;
	//</ModuleItems>	
	public ASTNode transform(PriorityBlock node) throws TransformerException;
	public ASTNode transform(Production node) throws TransformerException;
	public ASTNode transform(ProductionItem node) throws TransformerException;
	public ASTNode transform(Attributes node) throws TransformerException;
	public ASTNode transform(Attribute node) throws TransformerException;
	//<ProductionItems>
	public ASTNode transform(Sort node) throws TransformerException;
	public ASTNode transform(Terminal node) throws TransformerException;
	public ASTNode transform(UserList node) throws TransformerException;
	//</ProductionItems>
	public ASTNode transform(Term node) throws TransformerException;
	//<Terms>
	public ASTNode transform(Cell node) throws TransformerException;
	public ASTNode transform(Collection node) throws TransformerException;
	//	<Collections>
	public ASTNode transform(Ambiguity node) throws TransformerException;
	public ASTNode transform(Bag node) throws TransformerException;
	public ASTNode transform(KSequence node) throws TransformerException;
	public ASTNode transform(List node) throws TransformerException;
	public ASTNode transform(ListOfK node) throws TransformerException;
	public ASTNode transform(Map node) throws TransformerException;
	public ASTNode transform(Set node) throws TransformerException;
	//	</Collections>
	public ASTNode transform(CollectionItem node) throws TransformerException;
	//	<CollectionItems>
	public ASTNode transform(BagItem node) throws TransformerException;
	public ASTNode transform(ListItem node) throws TransformerException;
	public ASTNode transform(MapItem node) throws TransformerException;
	public ASTNode transform(SetItem node) throws TransformerException;
	//	</CollectionItems>
	public ASTNode transform(Constant node) throws TransformerException;
	public ASTNode transform(Empty node) throws TransformerException;
	public ASTNode transform(Hole node) throws TransformerException;
	public ASTNode transform(KApp node) throws TransformerException;
	public ASTNode transform(KLabel node) throws TransformerException;
	public ASTNode transform(Rewrite node) throws TransformerException;
	public ASTNode transform(TermCons node) throws TransformerException;
	public ASTNode transform(Variable node) throws TransformerException;
	//</Terms>
	public String getName();
}
