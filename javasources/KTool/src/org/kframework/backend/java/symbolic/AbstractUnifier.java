package org.kframework.backend.java.symbolic;

import org.kframework.kil.matchers.MatcherException;


/**
 * @author AndreiS
 */
public abstract class AbstractUnifier implements Unifier {
	
	public void fail() {
		throw new MatcherException("unification failed");
	}


}
