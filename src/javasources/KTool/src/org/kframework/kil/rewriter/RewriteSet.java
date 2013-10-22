package org.kframework.kil.rewriter;

import org.kframework.kil.Rewrite;

import java.util.LinkedHashSet;

/**
 *  This class is used to represent a term rewriting system that we
 *  try to apply.  In the current SimpleRewriter (which is brain dead),
 *  we actually try to match the LHS of each Rewrite class in order,
 *  finding a Substitution, and applying said Substitution to the (copy of)
 *  RHS of the Rewrite.  Once there is a more efficient pattern matcher
 *  we will still use RewriteSet in the compilation stage.
 *
 *  Note that the Set is ordered (Rewrites added in order of priority).  This
 *  is accomplished by using a LinkedHashSet which keeps elements in order
 *  of insertion.  {@see java.util.LinkedHashSet}
 */
public class RewriteSet extends LinkedHashSet<Rewrite> {

  @Override
  public String toString(){
    StringBuilder acc = new StringBuilder("rewrite system {\n");
    for(Rewrite r : this){
      acc.append("  ");
      acc.append(r);
      acc.append("\n");
    } 
    acc.append("}\n");
    return acc.toString();
  }
}
