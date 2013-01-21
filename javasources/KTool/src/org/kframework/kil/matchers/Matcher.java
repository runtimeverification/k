package org.kframework.kil.matchers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
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
import org.kframework.kil.FreezerSubstitution;
import org.kframework.kil.FreezerVariable;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabel;
import org.kframework.kil.KSequence;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.KList;
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

public interface Matcher {
	public void match(ASTNode node, ASTNode node2);
	public void match(Definition node, ASTNode node2);
	public void match(DefinitionItem node, ASTNode node2);
	// <DefinitionItems>
	public void match(LiterateDefinitionComment node, ASTNode node2);
	public void match(Module node, ASTNode node2);
	public void match(Require require, ASTNode require2);
	// </DefinitionItems>
	public void match(ModuleItem node, ASTNode node2);
	// <ModuleItems>
	public void match(Import node, ASTNode node2);
	public void match(LiterateModuleComment node, ASTNode node2);
	public void match(Sentence node, ASTNode node2);
	// <Sentences>
	public void match(StringSentence node, ASTNode node2);
	public void match(Configuration node, ASTNode node2);
	public void match(Context node, ASTNode node2);
	public void match(Rule node, ASTNode node2);
	// </Sentences>
	public void match(Syntax node, ASTNode node2);
	public void match(PriorityExtended node, ASTNode node2);
	public void match(PriorityExtendedAssoc node, ASTNode node2);
	// <ModuleItems>
	public void match(PriorityBlock node, ASTNode node2);
	public void match(PriorityBlockExtended node, ASTNode node2);
	public void match(Production node, ASTNode node2);
	public void match(ProductionItem node, ASTNode node2);
	// <ProductionItems>
	public void match(Sort node, ASTNode node2);
	public void match(Terminal node, ASTNode node2);
	public void match(UserList node, ASTNode node2);
	// </ProductionItems>
	public void match(Term node, ASTNode node2);
	// <Terms>
	public void match(Cell node, ASTNode node2);
	public void match(Collection node, ASTNode node2);
	// <Collections>
	public void match(Ambiguity node, ASTNode node2);
	public void match(Bag node, ASTNode node2);
	public void match(KSequence node, ASTNode node2);
	public void match(List node, ASTNode node2);
	public void match(KList node, ASTNode node2);
	public void match(Map node, ASTNode node2);
	public void match(Set node, ASTNode node2);
	// </Collections>
	public void match(CollectionItem node, ASTNode node2);
	// <CollectionItems>
	public void match(BagItem node, ASTNode node2);
	public void match(ListItem node, ASTNode node2);
	public void match(MapItem node, ASTNode node2);
	public void match(SetItem node, ASTNode node2);
	// </CollectionItems>
	public void match(Constant node, ASTNode node2);
	public void match(Empty node, ASTNode node2);
	public void match(Hole node, ASTNode node2);
	public void match(FreezerHole node, ASTNode node2);
	public void match(KApp node, ASTNode node2);
	public void match(KLabel node, ASTNode node2);
	public void match(Rewrite node, ASTNode node2);
	public void match(TermCons node, ASTNode node2);
	public void match(Bracket node, ASTNode node2);
	public void match(Variable node, ASTNode node2);
	// </Terms>
	public void match(Attributes attributes, ASTNode attributes2);
	public void match(Attribute attribute, ASTNode attribute2);
	public void match(TermComment node, ASTNode node2);
	// Others
	public void match(KInjectedLabel kInjectedLabel, ASTNode kInjectedLabel2);
	public void match(Freezer f, ASTNode f2);
	public void match(FreezerVariable var, ASTNode var2);
	public void match(FreezerSubstitution subst, ASTNode subst2);
	public void match(BackendTerm term, ASTNode term2);

	public String getName();

  /** 
   * this is the result of the pattern matching, or null if matching fails
   */
  public java.util.Map<Variable, ASTNode> getSubstitution();
}
