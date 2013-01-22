package org.kframework.kil.rewriter;

import org.kframework.kil.Rewrite;
import org.kframework.kil.Term;

import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.matchers.MatcherException;
import org.kframework.kil.matchers.SimpleMatcher;

import org.kframework.kil.visitors.exceptions.TransformerException;

import org.kframework.compile.utils.Substitution;

/** 
 * This class implements Term Rewriting based on the
 * SimpleMatcher.  It is very dumb and slow.  Some would
 * be nicer and call it "naive" ;)
 */

public class SimpleRewriter {
  
  static Matcher matcher = new SimpleMatcher();

  /**
   * rewrite only rewrites one step
   *
   * returns null if no change
   *
   * @param RewriteSet trs is the term rewriting system, specified in order of rule priority
   * @param Term t is the term to rewrite one step
   */
  @SuppressWarnings("cast")
  static public Term rewrite(RewriteSet trs, Term t){
    Term out = null;
    for(Rewrite r : trs){
      try {
        r.getLeft().accept(matcher, t);
        Substitution substitution = new Substitution(matcher.getSubstitution());
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
   *  rewrite to a normal form.  Will return original term if no rewrite is performed
   *
   * @param RewriteSet trs is the term rewriting system, specified in order of rule priority
   * @param Term t is the term to rewrite one step
   */
  static public Term rewriteToNormalForm(RewriteSet trs, Term t){
    Term out = t;
    Term temp = t;
    do {
      out = temp;
      temp = rewrite(trs, out);
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
  static public Term rewriteN(RewriteSet trs, Term t, int n){
    Term out = t;
    Term temp = t;
    for(int i = 0; (i < n) && (temp != null); ++i){
      out = temp;
      temp = rewrite(trs, out);
    } 
    return out;
  }
}
