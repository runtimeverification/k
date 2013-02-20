package org.kframework.kil.matchers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.Map;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.List;
import java.util.ArrayList;

/**This represents a pattern that looks up values in a MapImpl
*  it should only appear on the LHS of rules
*/
public class MapLookupPattern extends Term {

  /** these are the lookups to perform on a given map
   */
  private List<Binding> lookups;
  /**this is what remains of the map in the pattern, for instance
   * &lt;env&gt; E:Map X |-&gt; V &lt;/env&gt;, E is the remainder 
   */
  private Variable remainder;

  public MapLookupPattern(Map m){
    java.util.List<Term> contents = m.getContents();
    lookups = new ArrayList<Binding>(contents.size());
    for(Term t : contents){
      
    } 
  }

  public MapLookupPattern(MapLookupPattern mp){

  }

  private MapLookupPattern(){}

  public static MapLookupPattern test = new MapLookupPattern();

  static {
    test.lookups = new ArrayList<Binding>();
    test.remainder = new Variable("E", "Map");
    test.lookups.add(new Binding(new Variable("x", "KLabel"), Constant.KLABEL("bar")));
    test.lookups.add(new Binding(new Variable("qqq", "KLabel"), Constant.KLABEL("cdr")));
    test.lookups.add(new Binding(Constant.KLABEL("car"), Constant.KLABEL("cdr")));
  }

  public List<Binding> getLookups(){
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
	public ASTNode accept(Transformer visitor) throws TransformerException {
		return visitor.transform(this);
	}

  @Override
  public void accept(Matcher matcher, Term toMatch){
    matcher.match(this, toMatch);
  }

  @Override
	public MapLookupPattern shallowCopy() {
		return new MapLookupPattern(this);
	}

}  

