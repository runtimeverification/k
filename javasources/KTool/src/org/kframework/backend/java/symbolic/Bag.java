package org.kframework.backend.java.symbolic;


import org.kframework.kil.ASTNode;

/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/17/13
 * Time: 12:51 PM
 * To change this template use File | Settings | File Templates.
 */
public class Bag extends Collection {

    /**
     * @return the lest upper bound in the subsorting graph.
     */
    @Override
    public String getSort() {
        return "";
    }

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        throw new UnsupportedOperationException();  //To change body of implemented methods use File | Settings | File Templates.
    }
}
