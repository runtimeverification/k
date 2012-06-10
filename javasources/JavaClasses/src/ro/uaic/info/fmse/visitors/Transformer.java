package ro.uaic.info.fmse.visitors;

import ro.uaic.info.fmse.k.*;

public interface Transformer {
	public ASTNode transform(ASTNode node);
	public ASTNode transform(Definition node);
	public ASTNode transform(DefinitionItem node);
	//<DefinitionItems>
	public ASTNode transform(LiterateDefinitionComment node);
	public ASTNode transform(Module node);
	//</DefinitionItems>    
	public ASTNode transform(ModuleItem node);
	//<ModuleItems>
	public ASTNode transform(Import node);
	public ASTNode transform(LiterateModuleComment node);
	public ASTNode transform(Sentence node);
	//	<Sentences>
	public ASTNode transform(Configuration node);
	public ASTNode transform(Context node);
	public ASTNode transform(Rule node);
	//	</Sentences>
	public ASTNode transform(Syntax node);
	//<ModuleItems>	
	public ASTNode transform(PriorityBlock node);
	public ASTNode transform(Production node);
	public ASTNode transform(ProductionItem node);
	public ASTNode transform(Attributes node);
	public ASTNode transform(Attribute node);
	//<ProductionItems>
	public ASTNode transform(Sort node);
	public ASTNode transform(Terminal node);
	public ASTNode transform(UserList node);
	//</ProductionItems>
	public ASTNode transform(Term node);
	//<Terms>
	public ASTNode transform(Cell node);
	public ASTNode transform(Collection node);
	//	<Collections>
	public ASTNode transform(Ambiguity node);
	public ASTNode transform(Bag node);
	public ASTNode transform(KSequence node);
	public ASTNode transform(List node);
	public ASTNode transform(ListOfK node);
	public ASTNode transform(Map node);
	public ASTNode transform(Set node);
	//	</Collections>
	public ASTNode transform(CollectionItem node);
	//	<CollectionItems>
	public ASTNode transform(BagItem node);
	public ASTNode transform(ListItem node);
	public ASTNode transform(MapItem node);
	public ASTNode transform(SetItem node);
	//	</CollectionItems>
	public ASTNode transform(Constant node);
	public ASTNode transform(Empty node);
	public ASTNode transform(Hole node);
	public ASTNode transform(KApp node);
	public ASTNode transform(KLabel node);
	public ASTNode transform(Rewrite node);
	public ASTNode transform(TermCons node);
	public ASTNode transform(Variable node);
	//</Terms>
}
