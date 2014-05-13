// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

public class LiterateDefinitionComment extends DefinitionItem implements LiterateComment {
    private String value;
    private LiterateCommentType lcType = LiterateCommentType.COMMON;

    public LiterateDefinitionComment(String value, LiterateCommentType lcType) {
        this.value = value;
        this.lcType = lcType;
    }

    public LiterateDefinitionComment(LiterateDefinitionComment literateDefinitionComment) {
        super(literateDefinitionComment);
        value = literateDefinitionComment.value;
        lcType = literateDefinitionComment.lcType;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    public void setValue(String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public LiterateCommentType getType() {
        return lcType;
    }

    @Override
    public LiterateDefinitionComment shallowCopy() {
        return new LiterateDefinitionComment(this);
    }

    @Override
    public String toString() {
        return "/*"+lcType+value+"*/";
    }
}
