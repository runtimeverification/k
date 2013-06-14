package org.kframework.backend.java.symbolic;

import org.kframework.kil.matchers.MatcherException;


/**
 * @author AndreiS
 */
public abstract class AbstractMatcher implements Matcher {
	
	public void fail() {
		throw new MatcherException("matching failed");
	}

}
