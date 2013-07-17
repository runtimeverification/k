package org.kframework.kil.rewriter;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Binding;
import org.kframework.kil.matchers.MapInsertPattern;
import org.kframework.kil.matchers.SetInsertPattern;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Map;

public class RewriteSubstitution extends CopyOnWriteTransformer {
	Map<Term, Term> substitution;
	public RewriteSubstitution(Map<Term, Term> substitution, Context context) {
		super("Substitution", context);
		this.substitution = substitution;
	}
	
  private MapImpl rewriteMap(MapInsertPattern mip){
    Variable remainder = mip.getRemainder(); 
    MapImpl map = (MapImpl) substitution.get(remainder);
    //if map is null something is wrong in the Matcher
    //or the rewrite was not compiled correctly
    assert map != null;       
    for(Binding b : mip.getInsertions()){
      Term newKey = substitution.get(b.getKey());
      Term newValue = substitution.get(b.getValue());
      //This is ugly,
      //TODO: replace Maps with identity map class
      //that returns the key if the key is not bound
      if(newKey == null) newKey = b.getKey();
      if(newValue == null) newValue = b.getValue();
      map.put(newKey, newValue); 
    }
    return map;
  }


  private SetImpl rewriteSet(SetInsertPattern sip){
    Variable remainder = sip.getRemainder(); 
    SetImpl set = (SetImpl) substitution.get(remainder);
    //if set is null something is wrong in the Matcher
    //or the rewrite was not compiled correctly
    assert set != null;       
    for(Term t : sip.getInsertions()){
      Term newValue = substitution.get(t);
      if(newValue == null) newValue = t;
      set.add(newValue); 
    }
    return set;
  }


  @SuppressWarnings("cast")
	@Override
	public ASTNode transform(Term node) throws TransformerException {
    if(node instanceof MapInsertPattern){
      return super.transform(rewriteMap((MapInsertPattern)node));
    }
    else if(node instanceof SetInsertPattern){
      return super.transform(rewriteSet((SetInsertPattern)node));
    }
    //put other builtin pattern types here
    else{
		  Term substitute = substitution.get(node);
		  if (substitute != null) 
			  node = substitute;
		  return super.transform(node);
    }
	}
}
