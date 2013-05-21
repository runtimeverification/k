package org.kframework.kil.matchers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cast;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.List;
import java.util.ArrayList;

/**This represents a pattern that looks up values in a SetImpl
*  it should only appear on the LHS of rules
*/
public class SetLookupPattern extends Term {

  /** these are the lookups to perform on a given map
   */
  private List<Term> lookups;
  /**this is what remains of the map in the pattern, for instance
   * &lt;env&gt; E:Set X |-&gt; V &lt;/env&gt;, E is the remainder 
   */
  private Variable remainder;

  /**
   * currently assumes no "..." in Sets
   */
  public SetLookupPattern(Set s){
    java.util.List<Term> contents = s.getContents();
    lookups = new ArrayList<Term>(contents.size());
    for(Term t : contents){
      if(t instanceof Variable){
        if(!(t.getSort().equals("Set")))
          throw new MatchCompilationException(
              "Variable in Set pattern does not have sort Set: " + t);
        if(remainder != null)
          throw new MatchCompilationException(
              "Set pattern has more than one remainder variable, i.e., "
            + " more than one variable at the top level: " + s);
        remainder = (Variable) t;  
      }      
      else if(t instanceof SetItem){
        SetItem si = (SetItem) t;
        lookups.add(si.getItem());
      }
      else {
        throw new MatchCompilationException(
            "Set pattern contains a Term that is neither a Variable of sort Set "
          + "nor a SetItem.  This is not supported.  Set is: " + s);
      }
    }
    //else if(remainder == null) handle ...?  This will be difficult since we need
    //to add a fresh variable to both sides of the Rule.  Easier if we do this
    //in an earlier kompile pass  
  }

  public SetLookupPattern(SetLookupPattern sp){
    lookups = sp.lookups;
    remainder = sp.remainder;
  }

  public List<Term> getLookups(){
    return lookups;
  }

  public Variable getRemainder() {
    return remainder;
  }

  public String toString(){
    return "mapLookUpPattern(" 
      + lookups.toString() + ", " 
      + remainder + ")"
      ; 
  }

  @Override
	public void accept(Visitor visitor) {
		visitor.visit(this);
	}

  @Override
	public ASTNode accept(Transformer transformer) throws TransformerException {
		return transformer.transform(this);
	}

  @Override
  public void accept(Matcher matcher, Term toMatch){
    matcher.match(this, toMatch);
  }

  @Override
	public SetLookupPattern shallowCopy() {
		return new SetLookupPattern(this);
	}
 
	@Override
	public int hashCode() {
		//TODO: finish implementation
		return 0;
	}
 
  @Override
	public boolean equals(Object o) {
		if (o == null)
			return false;
		if (this == o)
			return true;
		if (!(o instanceof Cast))
			return false;
		// TODO: finish implementing this equals
		return true;
	}
}  

