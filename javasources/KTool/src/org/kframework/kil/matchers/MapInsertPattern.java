package org.kframework.kil.matchers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Map;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.List;
import java.util.ArrayList;

/**This represents a pattern that inserts bindings into a MapImpl
 * it should only appear on the RHS of rules
 */
public class MapInsertPattern extends Term {

  /**these are the lookups to perform on a given map
   */
  private List<Binding> insertions;
  /**this is what remains of the map in the pattern, for instance
  * &lt;env&gt; E:Map X |-&gt; V &lt;/env&gt;, E is the remainder
  */ 
  private Variable remainder;

  public MapInsertPattern(Map m){
    java.util.List<Term> contents = m.getContents();
    insertions = new ArrayList<Binding>(contents.size());
    for(Term t : contents){
      
    } 
  }

  public MapInsertPattern(MapInsertPattern mp){

  }

  public List<Binding> getInsertions(){
    return insertions;
  }

  public Variable getRemainder() {
    return remainder;
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
	public MapInsertPattern shallowCopy() {
		return new MapInsertPattern(this);
	}

}  

