package org.kframework.backend.java.symbolic;

import org.kframework.kil.matchers.MatcherException;


/**
 * Created with IntelliJ IDEA. User: andrei Date: 3/4/13 Time: 11:28 AM To change this template use File | Settings | File Templates.
 */
public abstract class AbstractMatcher implements Matcher {
	
	public void fail() {
		throw new MatcherException("matching failed");
	}

}
