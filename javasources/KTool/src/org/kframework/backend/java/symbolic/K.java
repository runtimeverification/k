package org.kframework.backend.java.symbolic;

import org.kframework.kil.ASTNode;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/18/13
 * Time: 12:18 PM
 * To change this template use File | Settings | File Templates.
 */
public class K extends Term {

    private final KLabel kLabel;
    private final KList kList;

    public K(KLabel kLabel, KList kList) {
        super("K");

        this.kLabel = kLabel;
        this.kList = kList;
    }

    public KLabel getKLabel() {
        return kLabel;
    }

    public KList getKList() {
        return kList;
    }

    @Override
    public boolean isSymbolic() {
        return kLabel.isFunction();
    }

    @Override
    public String toString() {
        String kListString = kList.toString();
        return !kListString.isEmpty() ? kLabel + "(" + kListString + ")" : kLabel.toString();
    }

    /**
     * @return a copy of the ASTNode containing the same fields.
     */
    @Override
    public ASTNode shallowCopy() {
        return new K(this.kLabel, this.kList);
    }

    @Override
    public void accept(Matcher matcher, Term patten) {
        matcher.match(this, patten);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

}
