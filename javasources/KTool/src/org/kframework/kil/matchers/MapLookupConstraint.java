package org.kframework.kil.matchers;

import org.kframework.kil.Term;
import org.kframework.kil.rewriter.MapImpl;

/**
 * This is a class to store MapLookups that need to be unified at a future
 * time because the binding for the Variable used as a key is not known at the
 * time the MapLookupPattern is initially tried
 */
public class MapLookupConstraint {
  private MapImpl map;
  private Term image; 

  public MapLookupConstraint(MapImpl map, Term image){
    this.map = map;
    this.image = image;
  }

  public String toString(){
    return "MapLookupConstraint(map=" + map + ", " + "image=" + image; 
  }

  /**
   * This method attempt to unify a given MapLookupPattern image
   * (i.e., the part on the rhs of the binding; denoted by the private 
   * variable image) with the value looked up in a MapImpl.  The Term t
   * passed is the key that should be looked up to obtain the Term which
   * we will attempt to unify with the stored Term (again, image) that is
   * passed it at the time the MapLookupConstraint is created 
   *
   * unification is attempted by using the current Matcher, which is passed in.
   * (recall that the Matcher stores the substitution)
   */
  public void unify(Matcher m, Term t){
    image.accept(m, map.get(t));
    //we remove the t as a key from the map since there
    //is no way a key can appear twice in a map.  This will
    //be more tricky in multimaps, if we ever have those
    map.remove(t);
  }
}
