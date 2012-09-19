package org.kframework.visitors;

import org.kframework.exceptions.TransformerException;
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
import org.kframework.k.Rewrite;
import org.kframework.k.Rule;
import org.kframework.k.Sentence;
import org.kframework.k.Set;
import org.kframework.k.SetItem;
import org.kframework.k.Sort;
import org.kframework.k.Syntax;
import org.kframework.k.Term;
import org.kframework.k.TermCons;
import org.kframework.k.Terminal;
import org.kframework.k.UserList;
import org.kframework.k.Variable;

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
