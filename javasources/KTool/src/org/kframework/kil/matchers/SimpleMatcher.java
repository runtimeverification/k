package org.kframework.kil.matchers;

import org.kframework.kil.*;

import java.util.HashMap;

public class SimpleMatcher implements Matcher {
 
  private java.util.Map<Variable, ASTNode> substitution = new HashMap<Variable, ASTNode>(); 

	public void match(ASTNode node, ASTNode node2) {
    throw new MatcherException("ASTNode cannot be matched directly");
  }

	public void match(Definition node, ASTNode node2){
    throw new MatcherException("Definition does not have a pattern match implementation.");
  }

	public void match(DefinitionItem node, ASTNode node2){
    throw new MatcherException("DefinitionItem does not have a pattern match implementation.");
  }

	// <DefinitionItems>
	public void match(LiterateDefinitionComment node, ASTNode node2){
    throw new MatcherException("LiterateDefinitionComment does not have a pattern match implementation.");
  }

	public void match(Module node, ASTNode node2){
    throw new MatcherException("Module does not have a pattern match implementation.");
  }

	public void match(Require require, ASTNode require2){
    throw new MatcherException("Require does not have a pattern match implementation.");
  }

	// </DefinitionItems>
	public void match(ModuleItem node, ASTNode node2){
    throw new MatcherException("ModuleItem does not have a pattern match implementation.");
  }

	// <ModuleItems>
	public void match(Import node, ASTNode node2){
    throw new MatcherException("Import does not have a pattern match implementation.");
  }

	public void match(LiterateModuleComment node, ASTNode node2){
    throw new MatcherException("LiterateModuleComment does not have a pattern match implementation.");
  }

	public void match(Sentence node, ASTNode node2){
    throw new MatcherException("Sentence does not have a pattern match implementation.");
  }

	// <Sentences>
	public void match(StringSentence node, ASTNode node2){
    throw new MatcherException("StringSentence does not have a pattern match implementation.");
  }

	public void match(Configuration node, ASTNode node2){
    throw new MatcherException("Configuration does not have a pattern match implementation.");
  }

	public void match(Context node, ASTNode node2){
    throw new MatcherException("Context does not have a pattern match implementation.");
  }

	public void match(Rule node, ASTNode node2){
    throw new MatcherException("Rule does not have a pattern match implementation.");
  }

	// </Sentences>
	public void match(Syntax node, ASTNode node2){
    throw new MatcherException("Syntax does not have a pattern match implementation.");
  }

	public void match(PriorityExtended node, ASTNode node2){
    throw new MatcherException("PriorityExtended does not have a pattern match implementation.");
  }

	public void match(PriorityExtendedAssoc node, ASTNode node2){
    throw new MatcherException("PriorityExtendedAssoc does not have a pattern match implementation.");
  }

	// <ModuleItems>
	public void match(PriorityBlock node, ASTNode node2){
    throw new MatcherException("PriorityBlock does not have a pattern match implementation.");
  }

	public void match(PriorityBlockExtended node, ASTNode node2){
    throw new MatcherException("PriorityBlockExtended does not have a pattern match implementation.");
  }

	public void match(Production node, ASTNode node2){
    throw new MatcherException("Production does not have a pattern match implementation.");
  }

	public void match(ProductionItem node, ASTNode node2){
    throw new MatcherException("ProductionItem does not have a pattern match implementation.");
  }

	// <ProductionItems>
	public void match(Sort node, ASTNode node2){
    throw new MatcherException("Sort does not have a pattern match implementation.");
  }

	public void match(Terminal node, ASTNode node2){
    throw new MatcherException("Terminal does not have a pattern match implementation.");
  }

	public void match(UserList node, ASTNode node2){
    throw new MatcherException("UserList does not have a pattern match implementation.");
  }

	// </ProductionItems>
	public void match(Term node, ASTNode node2){
    throw new MatcherException("Term does not have a pattern match implementation.");
  }

	// <Terms>
	public void match(Cell node, ASTNode node2){
    throw new MatcherException("Cell does not have a pattern match implementation.");
  }

	public void match(Collection node, ASTNode node2){
    throw new MatcherException("Collection does not have a pattern match implementation.");
  }

	// <Collections>
	public void match(Ambiguity node, ASTNode node2){
    throw new MatcherException("Ambiguity does not have a pattern match implementation.");
  }

	public void match(Bag node, ASTNode node2){
    throw new MatcherException("Bag does not have a pattern match implementation.");
  }

	public void match(KSequence node, ASTNode node2){
    throw new MatcherException("KSequence does not have a pattern match implementation.");
  }

	public void match(List node, ASTNode node2){
    throw new MatcherException("List does not have a pattern match implementation.");
  }

	public void match(KList node, ASTNode node2){
    if(!(node2 instanceof KList)){
      throw new MatcherException("Cannot match KList " + node + " to non-KList " + node2);
    }
    java.util.List<Term> tl1 = node.getContents();
    java.util.List<Term> tl2 = ((KList) node2).getContents();
    if(tl1.size() != tl2.size()){
      throw new MatcherException("Cannot match KLists " + node + " and " + node2 + " because they "
          + " have different sizes, is this an associative pattern? "
         +  " If so, those are currently unimplemented.");
    }
    for(int i = 0; i < tl1.size(); ++i) {
      tl1.get(i).accept(this, tl2.get(i));
    }
  }

	public void match(Map node, ASTNode node2){
    throw new MatcherException("Map does not have a pattern match implementation.");
  }

	public void match(Set node, ASTNode node2){
    throw new MatcherException("Set does not have a pattern match implementation.");
  }

	// </Collections>
	public void match(CollectionItem node, ASTNode node2){
    throw new MatcherException("CollectionItem does not have a pattern match implementation.");
  }

	// <CollectionItems>
	public void match(BagItem node, ASTNode node2){
    throw new MatcherException("BagItem does not have a pattern match implementation.");
  }

	public void match(ListItem node, ASTNode node2){
    throw new MatcherException("ListItem does not have a pattern match implementation.");
  }

	public void match(MapItem node, ASTNode node2){
    throw new MatcherException("MapItem does not have a pattern match implementation.");
  }

	public void match(SetItem node, ASTNode node2){
    throw new MatcherException("SetItem does not have a pattern match implementation.");
  }

	// </CollectionItems>
	public void match(Constant node, ASTNode node2){
    if(!(node2 instanceof Constant))
      throw new MatcherException("Attempted to match Constant " + node + " with non-Constant " + node2);
    if(!node.equals(node2)) 
      throw new MatcherException("Constants " + node + " and " + node2 + " do not match."); 
  }

	public void match(Empty node, ASTNode node2){
    throw new MatcherException("Empty does not have a pattern match implementation.");
  }

	public void match(Hole node, ASTNode node2){
    throw new MatcherException("Hole does not have a pattern match implementation.");
  }

	public void match(FreezerHole node, ASTNode node2){
    throw new MatcherException("FreezerHole does not have a pattern match implementation.");
  }

	public void match(KApp node, ASTNode node2){
    if(!(node2 instanceof KApp)){
      throw new MatcherException("Attemped to match KApp " + node  + " with non-KApp " + node2);
    }
    KApp ka2 = (KApp) node2; 
    node.getLabel().accept(this, ka2.getLabel());
    node.getChild().accept(this, ka2.getChild());
  }

	public void match(KLabel node, ASTNode node2){
    throw new MatcherException("KLabel does not have a pattern match implementation.");
  }

	public void match(Rewrite node, ASTNode node2){
    throw new MatcherException("Rewrite does not have a pattern match implementation.");
  }

	public void match(TermCons node, ASTNode node2){
    throw new MatcherException("TermCons does not have a pattern match implementation.");
  }

	public void match(Bracket node, ASTNode node2){
    throw new MatcherException("Bracket does not have a pattern match implementation.");
  }

	public void match(Variable node, ASTNode node2){
    ASTNode bound = substitution.get(node);

    if(bound == null){
      //this Term versus ASTNode is rather broken
      if(!(node2 instanceof Term)){
        substitution.put(node, node2);
        return;
      }
      Term t;
      t = (Term) node2;
      if(node.getSort().equals(t.getSort())){
        substitution.put(node, node2);
      } else {
        throw new MatcherException("Sort " + node.getSort() + " of Variable " + node + " does not match "
          + " sort " + t.getSort() + " of ASTNode " + node2); 
      }
    }

    else {
      if(!bound.equals(node2))
        throw new MatcherException("Non-linear pattern binds different terms, " + bound + " and " + node2 
            + ", to same Variable, " + node);
    }
 
  }

	// </Terms>
	public void match(Attributes attributes, ASTNode attributes2){
    throw new MatcherException("Attributes does not have a pattern match implementation.");
  }

	public void match(Attribute attribute, ASTNode attribute2){
    throw new MatcherException("Attribute does not have a pattern match implementation.");
  }

	public void match(TermComment node, ASTNode node2){
    throw new MatcherException("TermComment does not have a pattern match implementation.");
  }

	// Others
	public void match(KInjectedLabel kInjectedLabel, ASTNode kInjectedLabel2){
    throw new MatcherException("KInjectedLabel does not have a pattern match implementation.");
  }

	public void match(Freezer f, ASTNode f2){
    throw new MatcherException("Freezer does not have a pattern match implementation.");
  }

	public void match(FreezerVariable var, ASTNode var2){
    throw new MatcherException("FreezerVariable does not have a pattern match implementation.");
  }

	public void match(FreezerSubstitution subst, ASTNode subst2){
    throw new MatcherException("FreezerSubstitution does not have a pattern match implementation.");
  }

	public void match(BackendTerm term, ASTNode term2){
    throw new MatcherException("BackendTerm does not have a pattern match implementation.");
  }


	public String getName() { 
    return "SimpleMatcher"; 
  }

  public java.util.Map<Variable, ASTNode> getSubstitution() { 
    return substitution; 
  }
  
  public static void main(String[] args){
    KList patternGuts = new KList();
    KList termGuts = new KList();
    patternGuts.add(new Variable("x", "KLabel"));
    patternGuts.add(new Variable("y", "KLabel"));
    patternGuts.add(new Variable("z", "KLabel"));
    patternGuts.add(new Variable("x", "KLabel"));
    termGuts.add(Constant.KLABEL("a"));
    termGuts.add(Constant.KLABEL("b"));
    termGuts.add(Constant.KLABEL("c"));
    termGuts.add(Constant.KLABEL("a"));
    KApp pattern = new KApp(Constant.KLABEL("foo"), patternGuts);
    KApp term = new KApp(Constant.KLABEL("foo"), termGuts);
    System.out.println(pattern);
    System.out.println(term);
    Matcher m = new SimpleMatcher();
    pattern.accept(m, term);
    System.out.println(m.getSubstitution());
  }
}
