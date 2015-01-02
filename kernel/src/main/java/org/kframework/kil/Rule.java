// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;


/**
 * A rule declaration.
 * The left and right hand sides of the rewrite are described by the single term
 * {@code body} which allows {@link Rewrite} nodes to describe the changes.
 * Any explicit attributes on the rule are stored in {@link #attributes}.
 */
public class Rule extends Sentence {

    public Rule(Element element, JavaClassesFactory factory) {
        super(element, factory);
    }

    public Rule(Rule node) {
        super(node);
    }

    public Rule() {
        super();
    }

    public Rule(Term lhs, Term rhs, Context context) {
        super();
        this.setBody(new Rewrite(lhs, rhs, context));
    }

    public Rule(Term lhs, Term rhs, Term requires, Term ensures, Context context) {
        this(lhs, rhs, context);
        this.setRequires(requires);
        this.setEnsures(ensures);
    }

    public Rule(Sentence term) {
        super(term);
    }

    public String toString() {
        String content = "  rule ";

        if (this.label != null && !this.label.equals(""))
            content += "[" + this.label + "]: ";

        content += this.body + " ";
        if (this.requires != null) {
            content += "requires " + this.requires + " ";
        }
        if (this.ensures != null) {
            content += "ensures " + this.ensures + " ";
        }

        return content + getAttributes();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Rule shallowCopy() {
        return new Rule(this);
    }

}
