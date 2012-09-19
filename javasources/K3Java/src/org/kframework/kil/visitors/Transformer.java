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
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.exceptions.TransformerException;

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
