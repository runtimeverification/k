package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.matchers.Matchable;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/17/13
 * Time: 12:56 PM
 * To change this template use File | Settings | File Templates.
 */
public abstract class Term extends ASTNode implements Matchable {
    /**
     * @return the lest upper bound in the subsorting graph.
     */
    public abstract String getSort();
}
