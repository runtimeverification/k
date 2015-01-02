// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.Visitor;
import org.w3c.dom.Element;

/**
 * Configuration declaration.
 * The term {@code body} is the intial configuration as a bag of cells,
 * also allowing cell attributes and variables such as {@code $PGM}.
 * May not have a non-null {@code condition}.
 */
public class Configuration extends Sentence {

    public Configuration() {
        super();
    }

    public Configuration(Element element, JavaClassesFactory factory) {
        super(element, factory);
    }

    public Configuration(Configuration node) {
        super(node);
    }

    public Configuration(Sentence term) {
        super(term);
    }

    public String toString() {
        String content = "  configuration ";
        content += this.body + " ";
        return content;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public Configuration shallowCopy() {
        return new Configuration(this);
    }
}
