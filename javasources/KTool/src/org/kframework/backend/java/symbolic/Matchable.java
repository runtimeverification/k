package org.kframework.backend.java.symbolic;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/24/13
 * Time: 5:34 PM
 * To change this template use File | Settings | File Templates.
 */
public interface Matchable {
    /**
     *  Implements a visitor pattern specialized for matching.
     *
     *  @param matcher
     *  @param patten
     */
    public void accept(Matcher matcher, Term patten);
}
