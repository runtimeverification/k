// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

/**
 * A rule, configuration declaration, or context.
 * Each parses as a term, this class declares common members
 * {@link #body} and {@link #requires}, which have different
 * interpretations in the subclasses.
 */
public class Sentence extends ModuleItem {
    /** Label from {@code rule[}label{@code ]:} syntax or "". Currently unrelated to attributes */
    String label = "";

    public Sentence(Sentence s) {
        super(s);
        this.label = s.label;
    }

    public Sentence() {
        super();
    }

    @Override
    public Sentence shallowCopy() {
        return new Sentence(this);
    }

    public String getLabel() {
        return label;
    }

    public void setLabel(String label) {
        this.label = label;
    }

}
