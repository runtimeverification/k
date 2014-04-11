package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/** An import directive */
public class Import extends ModuleItem {

    String name;

    public Import(String importName) {
        super();
        name = importName;
    }

    public Import(Import import1) {
        super(import1);
        this.name = import1.name;
    }

    @Override
    public String toString() {
        return "  imports " + name;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    @Override
    public Import shallowCopy() {
        return new Import(this);
    }
    
    @Override
    public <P, R> R accept(Visitor<P, R> visitor, P p) {
        return visitor.visit(this, p);
    }
}
