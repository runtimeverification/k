package org.kframework.kil.matchers;

import org.kframework.kil.Term;

public interface Matchable {
  /**
   *  Implements a specialized Visitor pattern.
   *  Here the matcher will accept a term, rather than operating only on
   *  the this pointer, as would a normal Visitor
   *
   *  @param this - is the pattern to be matched
   *  @param toMatch is the term we are attempting to match against
   */
  public void accept(Matcher matcher, Term toMatch);
}
