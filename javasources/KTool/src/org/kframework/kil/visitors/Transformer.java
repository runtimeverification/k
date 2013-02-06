package org.kframework.kil.visitors;

import org.kframework.kil.*;
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
	public ASTNode transform(StringSentence node) throws TransformerException;
	public ASTNode transform(Configuration node) throws TransformerException;
	public ASTNode transform(Context node) throws TransformerException;
	public ASTNode transform(Rule node) throws TransformerException;
	//	</Sentences>
	public ASTNode transform(Syntax node) throws TransformerException;
	public ASTNode transform(PriorityExtended node) throws TransformerException;
	public ASTNode transform(PriorityExtendedAssoc node) throws TransformerException;
	//</ModuleItems>	
	public ASTNode transform(PriorityBlock node) throws TransformerException;
	public ASTNode transform(PriorityBlockExtended node) throws TransformerException;
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
	public ASTNode transform(KList node) throws TransformerException;
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
	public ASTNode transform(KInjectedLabel node) throws TransformerException;
	public ASTNode transform(FreezerLabel node) throws TransformerException;
	public ASTNode transform(Rewrite node) throws TransformerException;
	public ASTNode transform(TermCons node) throws TransformerException;
	public ASTNode transform(Bracket node) throws TransformerException;
	public ASTNode transform(Variable node) throws TransformerException;
	public ASTNode transform(Freezer node) throws TransformerException;
	public ASTNode transform(FreezerVariable node) throws TransformerException;
	public ASTNode transform(FreezerSubstitution node) throws TransformerException;
	public ASTNode transform(BackendTerm term) throws TransformerException;
	//</Terms>
	public String getName();
}
