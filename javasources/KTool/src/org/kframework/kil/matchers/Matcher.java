package org.kframework.kil.matchers;

import org.kframework.kil.Ambiguity;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Empty;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerHole;
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
import org.kframework.kil.rewriter.SetImpl;

/**
 * This is the interface for recursive pattern matching.  It is used
 * somewhat like a Visitor.
 *
 * I have changed the order of definition from Visitor to be alphabetical
 * order by kil class, e.g., handling Ambiguity is the first method
 */
public interface Matcher {
	public void match(Ambiguity term, Term term2);
	public void match(BackendTerm term, Term term2);
	public void match(Bag term, Term term2);
	public void match(BagItem term, Term term2);
	public void match(Bracket term, Term term2);
	public void match(Cast term, Term term2);
	public void match(Cell term, Term term2);
	public void match(Empty term, Term term2);
	public void match(Freezer term, Term term2);
	public void match(FreezerHole term, Term term2);
	public void match(Hole term, Term term2);
	public void match(KApp term, Term term2);
	public void match(KInjectedLabel term, Term term2);
	public void match(KList term, Term term2);
	public void match(KSequence term, Term term2);
	public void match(List term, Term term2);
	public void match(ListItem term, Term term2);
	public void match(Map term, Term term2);
	public void match(MapItem term, Term term2);
	public void match(MapLookupPattern term, Term term2);
	public void match(MapInsertPattern term, Term term2);
	public void match(MapImpl term, Term term2);
	public void match(Rewrite term, Term term2);
	public void match(Set term, Term term2);
	public void match(SetItem term, Term term2);
	public void match(SetLookupPattern term, Term term2);
	public void match(SetInsertPattern term, Term term2);
	public void match(SetImpl term, Term term2);
	public void match(TermComment term, Term term2);
	public void match(TermCons term, Term term2);
	public void match(Variable term, Term term2);

	public String getName();

  /** 
   * this is the result of the pattern matching, or null if matching fails
   */
  public java.util.Map<Term, Term> getSubstitution();
  
  /**
   * this is the entry point for matching because there is some
   * setup tear down we need to do before and after the modified
   * visitor pattern runs
   */ 
  public void start(Term t1, Term t2);
}
