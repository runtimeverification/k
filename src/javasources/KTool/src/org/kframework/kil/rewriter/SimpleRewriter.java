package org.kframework.kil.rewriter;

//unit test imports

//end test imports

import org.kframework.kil.Rewrite;
import org.kframework.kil.Term;

        import org.kframework.kil.loader.Context;
        import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.matchers.MatcherException;
import org.kframework.kil.matchers.SimpleMatcher;

        import org.kframework.kil.visitors.exceptions.TransformerException;

/** 
 * This class implements Term Rewriting based on the
 * SimpleMatcher.  It is very dumb and slow.  Some would
 * be nicer and call it "naive" ;)
 */

public class SimpleRewriter {
  protected Context context;
  protected Matcher matcher;

  public SimpleRewriter(org.kframework.kil.loader.Context context) {
	  this.context = context;
	  matcher = new SimpleMatcher(context);
  }
  

  //we know the cast is safe because SimpleMatcher is only defined for Terms
  //This helper function returns null if no rewrite is performed
  @SuppressWarnings("cast")
   private Term rewriteAux(RewriteSet trs, Term t){
    Term out = null;
    for(Rewrite r : trs){
      try {
        matcher.start(r.getLeft(),t);
        RewriteSubstitution substitution = new RewriteSubstitution(matcher.getSubstitution(),
                context);
        try {
          //ignore warning, we know this must be a Term
          out = (Term) r.getRight().accept(substitution);
          break;
        }
        catch(TransformerException te){
          System.err.println("Failed to perform substitution on rhs " + r.getRight() + " with substitution " +
              matcher.getSubstitution());
          throw new RuntimeException(te);
        }
      }
      catch(MatcherException pe){
        continue;
      }
    }
    return out;
  }

  /**
   * rewrite only rewrites one step.  Will return original term if no rewrite is performed
   *
   * @param RewriteSet trs is the term rewriting system, specified in order of rule priority
   * @param Term t is the term to rewrite one step
   */
    public Term rewrite(RewriteSet trs, Term t){
     Term temp = rewriteAux(trs, t);
     return (temp == null)? t : temp;
   }

  /**
   *  rewrite to a normal form.  Will return original term if no rewrite is performed
   *
   * @param RewriteSet trs is the term rewriting system, specified in order of rule priority
   * @param Term t is the term to rewrite one step
   */
   public Term rewriteToNormalForm(RewriteSet trs, Term t){
    Term out = t;
    Term temp = t;
    do {
      out = temp;
      temp = rewriteAux(trs, out);
    }
    while(temp != null);
    return out;
  }

  /**
   *  rewrite n times.  Will return original term if no rewrite is performed
   *
   * @param RewriteSet trs is the term rewriting system, specified in order of rule priority
   * @param Term t is the term to rewrite one step
   * @param int n is the (max) number of rewrites to perform
   */
   public Term rewriteN(RewriteSet trs, Term t, int n){
    Term out = t;
    Term temp = t;
    for(int i = 0; (i <= n) && (temp != null); ++i){
      out = temp;
      temp = rewriteAux(trs, out);
    } 
    return out;
  }

  public static void main(String[] args){
      /*
    KList patternGuts = new KList();
    KList termGuts = new KList();
    KList subtermGuts = new KList();
    KList rhsGuts = new KList();
    patternGuts.add(new Variable("x", KSorts.KLABEL));
    patternGuts.add(new Variable("y", KSorts.KLABEL));
    patternGuts.add(new Variable("z", "K"));
    patternGuts.add(new Variable("x", KSorts.KLABEL));
    subtermGuts.add(Constant.KLABEL("d"));
    subtermGuts.add(Constant.KLABEL("e"));
    KApp subterm = new KApp(Constant.KLABEL("bar"), subtermGuts);
    termGuts.add(Constant.KLABEL("a"));
    termGuts.add(Constant.KLABEL("b"));
    termGuts.add(subterm);
    termGuts.add(Constant.KLABEL("a"));
    rhsGuts.add(Constant.KLABEL("42"));
    rhsGuts.add(new Variable("x", KSorts.KLABEL));
    rhsGuts.add(new Variable("z", "K"));
    KApp pattern = new KApp(Constant.KLABEL("foo"), patternGuts);
    KApp term = new KApp(Constant.KLABEL("foo"), termGuts);
    KApp rhs = new KApp(Constant.KLABEL("car"), rhsGuts);
    System.out.println(pattern);
    System.out.println(term);
    Matcher m = new SimpleMatcher();
    pattern.accept(m, term);
    System.out.println(m.getSubstitution());
    System.out.println("==================");
    RewriteSet trs = new RewriteSet();
    trs.add(new Rewrite(pattern, rhs));
    System.out.println(trs);
    System.out.println("==============>");
    System.out.println(rewrite(trs, term));
    System.out.println("==================");
    //add another rewrite that matches the rhs of the previous rewrite
    //and just rewrites to variable z
    trs.add(new Rewrite(rhs, new Variable("z", "K")));
    //add another rewrite that matches z from above (which is java variable subterm)
    trs.add(new Rewrite(subterm, Constant.KLABEL("DONE")));
    System.out.println(trs);
    System.out.println("rewrite 1: " + rewriteN(trs,term,1)); //should print same as last time
    System.out.println("rewrite 2: " + rewriteN(trs,term,2)); //should print bar(d ,, e)
    System.out.println("rewrite 3: " + rewriteN(trs,term,3)); //should print DONE
    System.out.println("rewrite normal form: " + rewriteToNormalForm(trs,term)); //should print DONE
    System.out.println("=========map rewrite==========");
    trs = new RewriteSet();
    MapItem lm1 = new MapItem(Constant.KLABEL("bar"), Constant.KLABEL("foo"));
    MapItem rm1 = new MapItem(Constant.KLABEL("ouch"), Constant.KLABEL("hcuo"));
    Variable rem = new Variable("E", "Map"); 
    List<Term> lmg = new ArrayList<Term>();
    List<Term> rmg = new ArrayList<Term>();
    lmg.add(lm1);
    lmg.add(rem);
    rmg.add(rm1);
    rmg.add(rem);
    MapLookupPattern l = new MapLookupPattern(new Map(lmg));
    MapInsertPattern r = new MapInsertPattern(new Map(rmg));
    System.out.println(l);
    System.out.println(r);
    trs.add(new Rewrite(l,r));
    System.out.println(trs);
    MapImpl mi = new MapImpl();
    mi.put(Constant.KLABEL("bar"), Constant.KLABEL("foo"));
    mi.put(Constant.KLABEL("car"), Constant.KLABEL("foo"));
    mi.put(Constant.KLABEL("sar"), Constant.KLABEL("foo"));
    System.out.println("initial: " + mi);
    System.out.println("normal form: " + rewriteToNormalForm(trs, mi));
    System.out.println("========more complicated map rewrite========");
    patternGuts.add(l);
    rhsGuts.add(r);
    termGuts.add(mi);
    mi.remove(Constant.KLABEL("ouch"));
    mi.put(Constant.KLABEL("bar"), Constant.KLABEL("foo"));
    trs = new RewriteSet();
    pattern = new KApp(Constant.KLABEL("foo"), patternGuts);
    term = new KApp(Constant.KLABEL("foo"), termGuts);
    rhs = new KApp(Constant.KLABEL("car"), rhsGuts);
    trs.add(new Rewrite(pattern, rhs));
    System.out.println(trs); 
    System.out.println("initial: " + term);

    System.out.println("normal form: " + rewriteToNormalForm(trs, term));
    */
  }
}
