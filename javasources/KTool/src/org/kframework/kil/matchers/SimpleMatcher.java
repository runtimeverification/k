package org.kframework.kil.matchers;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cell;
import org.kframework.kil.Constant;
import org.kframework.kil.Empty;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.FreezerSubstitution;
import org.kframework.kil.FreezerVariable;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.List;
import org.kframework.kil.ListItem;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Set;
import org.kframework.kil.SetItem;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.rewriter.MapImpl;

import java.util.HashMap;
import java.util.HashSet;
import java.util.ArrayList;

public class SimpleMatcher implements Matcher {
 
  private java.util.Map<Term, Term> substitution 
    = new HashMap<Term, Term>(); 

  private java.util.Map<Variable, HashSet<MapLookupConstraint>> deferredMapLookups 
    = new HashMap<Variable, HashSet<MapLookupConstraint>>();

	@Override
  public void match(Ambiguity term, Term term2){
    throw new MatcherException("Ambiguity does not have a pattern match implementation.");
  }

	@Override
  public void match(BackendTerm term, Term term2){
    throw new MatcherException("BackendTerm does not have a pattern match implementation.");
  }

	@Override
  public void match(Bag term, Term term2){
    throw new MatcherException("Bag does not have a pattern match implementation.");
  }

	@Override
  public void match(BagItem term, Term term2){
    throw new MatcherException("BagItem does not have a pattern match implementation.");
  }

	@Override
  public void match(Bracket term, Term term2){
    throw new MatcherException("Bracket does not have a pattern match implementation.");
  }

	@Override
  public void match(Cell term, Term term2){
    throw new MatcherException("Cell does not have a pattern match implementation.");
  }

	@Override
  public void match(Constant term, Term term2){
    if(!(term2 instanceof Constant))
      throw new MatcherException("Attempted to match Constant " + term + " with non-Constant " + term2);
    if(!term.equals(term2)) 
      throw new MatcherException("Constants " + term + " and " + term2 + " do not match."); 
  }

	@Override
  public void match(Empty term, Term term2){
    if(!(term2 instanceof Empty)){
      throw new MatcherException("Attempted to match Empty with " + term2 + ".");
    }
  }

	@Override
  public void match(Freezer term, Term term2){
    throw new MatcherException("Freezer does not have a pattern match implementation.");
  }

	@Override
  public void match(FreezerHole term, Term term2){
    throw new MatcherException("FreezerHole does not have a pattern match implementation.");
  }

	@Override
  public void match(FreezerSubstitution subst, Term subst2){
    throw new MatcherException("FreezerSubstitution does not have a pattern match implementation.");
  }

	@Override
  public void match(FreezerVariable var, Term var2){
    throw new MatcherException("FreezerVariable does not have a pattern match implementation.");
  }

	@Override
  public void match(Hole term, Term term2){
    throw new MatcherException("Hole does not have a pattern match implementation.");
  }

	@Override
  public void match(KApp term, Term term2){
    if(!(term2 instanceof KApp)){
      throw new MatcherException("Attemped to match KApp " + term  + " with non-KApp " + term2);
    }
    KApp ka2 = (KApp) term2; 
    term.getLabel().accept(this, ka2.getLabel());
    term.getChild().accept(this, ka2.getChild());
  }

	@Override
  public void match(KInjectedLabel term, Term term2){
    throw new MatcherException("KInjectedLabel does not have a pattern match implementation.");
  }

	@Override
  public void match(KList term, Term term2){
    if(!(term2 instanceof KList)){
      throw new MatcherException("Cannot match KList " + term + " to non-KList " + term2);
    }
    java.util.List<Term> tl1 = term.getContents();
    java.util.List<Term> tl2 = ((KList) term2).getContents();
    if(tl1.size() != tl2.size()){
      throw new MatcherException("Cannot match KLists " + term + " and " + term2 + " because they "
          + " have different sizes, is this an associative pattern? "
         +  " If so, those are currently unimplemented.");
    }
    for(int i = 0; i < tl1.size(); ++i) {
      tl1.get(i).accept(this, tl2.get(i));
    }
  }

	@Override
  public void match(KSequence term, Term term2){
    throw new MatcherException("KSequence does not have a pattern match implementation.");
  }

	@Override
  public void match(List term, Term term2){
    throw new MatcherException("List does not have a pattern match implementation.");
  }

	@Override
  public void match(ListItem term, Term term2){
    throw new MatcherException("ListItem does not have a pattern match implementation.");
  }

	@Override
  public void match(Map term, Term term2){
    throw new MatcherException("Map does not have a pattern match implementation.");
  }

	@Override
  public void match(MapItem term, Term term2){
    throw new MatcherException("MapItem does not have a pattern match implementation.");
  }

	@Override
  public void match(MapLookupPattern term, Term term2){
    if(!(term2 instanceof MapImpl)){
      throw new MatcherException("Attempted to match a MapLookupPattern with non MapImpl: " 
          + term2);  
    }
    MapImpl map = (MapImpl) term2;
    for(Binding b : term.getLookups()){
      Term key = b.getKey();
      if(key instanceof Variable){
        key = substitution.get(key);
        //if key is null we have not bound this Variable yet
        //and must create a deferredMapLookup
        if(key == null){
          MapLookupConstraint mlc = new MapLookupConstraint(map, b.getValue());
          HashSet<MapLookupConstraint> constraints = deferredMapLookups.get(b.getKey());
          if(constraints == null){
            constraints = new HashSet<MapLookupConstraint>();
            deferredMapLookups.put((Variable) b.getKey(), constraints);
          }
          constraints.add(mlc);
          //we cannot remove the key until the constraint is unified
          //since we do not want to have to copy maps
          //I will make some concessions to performance here....
          //I am not happy with how MatchLookupContraint.unify does
          //some key removal while others are performed manually
          //in this method.  Consider refactoring
        }
        // yay, we know the binding so we can just unify without deferring!
        else {
          b.getValue().accept(this, map.get(key));
          //we must remove the key so that we can properly bind the 
          //remainder
          map.remove(key);
        }
      } 
      //here we are looking up with a Term that wasn't even a Variable, so this is
      //really simple
      else{
        b.getValue().accept(this, map.get(b.getKey()));
        //we must remove the key so that we can properly bind the 
        //remainder
        map.remove(key);
      }
    }
    substitution.put(term.getRemainder(), map);
  }

	@Override
  public void match(MapInsertPattern term, Term term2){
    throw new MatcherException("MapInsertPattern does not have a pattern match implementation.");
  }

	@Override
  public void match(MapImpl term, Term term2){
    throw new MatcherException("MapImpls can never appear in patterns, only in " +
        "Terms that we are actually rewriting or on rule RHS.");
  }

	@Override
  public void match(Rewrite term, Term term2){
    throw new MatcherException("Rewrite should never appear within a term we are pattern matching. "
        + "Offending term: " + term);
  }

	@Override
  public void match(Set term, Term term2){
    throw new MatcherException("Set does not have a pattern match implementation.  "
        + "Offending term: " + term);
  }

	@Override
  public void match(SetItem term, Term term2){
    throw new MatcherException("SetItem does not have a pattern match implementation.  "
       + "Offending term: " + term);
  }

	@Override
  public void match(TermComment term, Term term2){
    throw new MatcherException("TermComment does not have a pattern match implementation.");
  }


	@Override
  public void match(TermCons term, Term term2){
    throw new MatcherException("TermCons does not have a pattern match implementation.");
  }


	@Override
  public void match(Variable term, Term term2){
    Term bound = substitution.get(term);

    if(bound == null){
      //this Term versus Term is rather broken
      if(!(term2 instanceof Term)){
        substitution.put(term, term2);
        return;
      }
      Term t;
      t = (Term) term2;
      if(term.getSort().equals(t.getSort())){
        substitution.put(term, term2);
      } else {
        throw new MatcherException("Sort " + term.getSort() 
            + " of Variable " + term + " does not match "
          + " sort " + t.getSort() + " of Term " + term2); 
      }
      //handle any deferred Map lookups where we did not 
      //know the Variable binding before hand
      //since we just bound a Variable
      HashSet<MapLookupConstraint> lookups = deferredMapLookups.get(term); 
      if(lookups == null) return;
      for(MapLookupConstraint lookup : lookups){
        //look unify the value bound to term2 in the MapImpl with the image 
        //in the MapLookupPattern 
        lookup.unify(this, term2);
      }
      //this is necessary because we need to determine if we have actually
      //matched a pattern based on if there is anything left in the deferredMapLookups
      deferredMapLookups.remove(term); 
    }

    else {
      if(!bound.equals(term2))
        throw new MatcherException("Non-linear pattern binds different terms, " + bound + " and " + term2 
            + ", to same Variable, " + term);
    }
 
  }

	@Override
  public String getName() { 
    return "SimpleMatcher"; 
  }

  @Override
  public java.util.Map<Term, Term> getSubstitution() { 
    return substitution; 
  }

  @Override
  public void start(Term t1, Term t2){
    //set up
    substitution.clear();
    deferredMapLookups.clear(); 
    //run visitor pattern
    t1.accept(this, t2);
    //tear down
    if(deferredMapLookups.size() != 0) {
      System.out.println("current subst: " + substitution);
     throw new MatcherException("deferredMapLookups not empty, not all variables were discovered, pattern does not match: " +
        deferredMapLookups); 
    }
  }
  
  public static void main(String[] args){
    KList patternGuts = new KList();
    KList termGuts = new KList();
    KList subtermGuts = new KList();
    patternGuts.add(new Variable("x", "KLabel"));
    patternGuts.add(new Variable("y", "KLabel"));
    patternGuts.add(new Variable("z", "K"));
    patternGuts.add(new Variable("x", "KLabel"));
    subtermGuts.add(Constant.KLABEL("d"));
    subtermGuts.add(Constant.KLABEL("e"));
    KApp subterm = new KApp(Constant.KLABEL("bar"), subtermGuts);
    termGuts.add(Constant.KLABEL("a"));
    termGuts.add(Constant.KLABEL("b"));
    termGuts.add(subterm);
    termGuts.add(Constant.KLABEL("a"));
    KApp pattern = new KApp(Constant.KLABEL("foo"), patternGuts);
    KApp term = new KApp(Constant.KLABEL("foo"), termGuts);
    System.out.println(pattern);
    System.out.println(term);
    Matcher m = new SimpleMatcher();
    m.start(pattern, term);
    System.out.println(m.getSubstitution());
    System.out.println("\n====map test");
    MapLookupPattern test = MapLookupPattern.test;
    MapImpl map = new MapImpl();
    map.put(Constant.KLABEL("foo"), Constant.KLABEL("bar"));
    map.put(Constant.KLABEL("car"), Constant.KLABEL("cdr"));
    map.put(Constant.KLABEL("a"), Constant.KLABEL("bar"));
    map.put(Constant.KLABEL("d"), Constant.KLABEL("cdr"));
    patternGuts.add(test);
    patternGuts.add(new Variable("qqq", "KLabel"));
    termGuts.add(map);
    termGuts.add(Constant.KLABEL("d"));
    pattern = new KApp(Constant.KLABEL("foo"), patternGuts);
    term = new KApp(Constant.KLABEL("foo"), termGuts);
    System.out.println("pattern: " + pattern);
    System.out.println("term: " + term);
    m.start(pattern, term);
    System.out.println("theta: " + m.getSubstitution());
  }
}
