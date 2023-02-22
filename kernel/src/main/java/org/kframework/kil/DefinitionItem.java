// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kil;

public abstract class DefinitionItem extends ASTNode {

    /** set iff the item was read from a file in the standard libraries */
    private boolean predefined;

    public DefinitionItem() {
        super();
    }

    public void setPredefined(boolean predefined) {
        this.predefined = predefined;
    }

    public boolean isPredefined() {
        return predefined;
    }
}
