package org.kframework.kil.matchers;

import org.kframework.kil.KLabelConstant;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cast;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.List;
import java.util.ArrayList;

/**This represents a pattern that inserts bindings into a MapImpl
 * it should only appear on the RHS of rules
 *
 * TODO: There is probably no reason to separate this from MapLookupPattern
 * unify to one class MapPattern?
 */
public class MapInsertPattern extends Term {

  /**these are the lookups to perform on a given map
   */
  private List<Binding> insertions;
  /**this is what remains of the map in the pattern, for instance
  * &lt;env&gt; E:Map X |-&gt; V &lt;/env&gt;, E is the remainder
  */ 
  private Variable remainder;

  public MapInsertPattern(Map m, Context context){
    java.util.List<Term> contents = m.getContents();
    insertions = new ArrayList<Binding>(contents.size());
    for(Term t : contents){
      if(t instanceof Variable){
        if(!(t.getSort().equals("Map")))
          throw new MatchCompilationException(
              "Variable in Map pattern does not have sort Map: " + t);
        if(remainder != null)
          throw new MatchCompilationException(
              "Map pattern has more than one remainder variable, i.e., "
            + " more than one variable at the top level: " + m);
        remainder = (Variable) t;  
      }      
      else if(t instanceof MapItem){
        MapItem mi = (MapItem) t;
        insertions.add(new Binding(mi.getKey(), mi.getValue()));
      }
      else {
        throw new MatchCompilationException(
            "Map pattern contains a Term that is neither a Variable of sort Map "
          + "nor a MapItem.  This is not supported.  Map is: " + m);
      }
    }
    //else if(remainder == null) handle ...?  This will be difficult since we need
    //to add a fresh variable to both sides of the Rule.  Easier if we do this
    //in an earlier kompile pass  
  }

  public MapInsertPattern(MapInsertPattern mp){
    insertions = mp.insertions;
    remainder = mp.remainder;
  }

  public List<Binding> getInsertions(){
    return insertions;
  }

  public Variable getRemainder() {
    return remainder;
  }

  public String toString(){
    return "mapInsertPattern(" 
      + insertions.toString() + ", " 
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
	public MapInsertPattern shallowCopy() {
		return new MapInsertPattern(this);
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

	@Override
	public Term kilToKore() {
		
		ArrayList<Term> tempList = new ArrayList<Term>();
		for(int i = 0;i<this.insertions.size();++i){
			
			Term tempKey = this.insertions.get(i).getKey();
			Term tempValue = this.insertions.get(i).getValue();
			
			ArrayList<Term> mapList = new ArrayList<Term>();
			mapList.add(tempKey);
			mapList.add(tempValue);
			
			KApp tempNode = new KApp((new KLabelConstant("_|->_")),(new KList(mapList)));
			tempList.add(tempNode);
		}
		
		KSequence firstNode = KSequence.adjust(new KList(tempList));
		KLabelConstant secondLabel = null;
		if(this.remainder.isFresh()){
			secondLabel = new KLabelConstant("?"+this.remainder.getName()+":"+this.remainder.getSort());
		} else {
			secondLabel = new KLabelConstant(this.remainder.getName()+":"+this.remainder.getSort());
		}
		
		ArrayList<Term> resultList = new ArrayList<Term>();
		resultList.add(firstNode);
		resultList.add(KSequence.adjust(secondLabel));
		return new KApp(new KLabelConstant("mapInsertPattern(_,_)"),new KList(resultList));
	}
}  

