// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

public class LiterateModuleComment extends ModuleItem implements LiterateComment {

    private String value;
    private LiterateCommentType lcType;

    public LiterateModuleComment(LiterateModuleComment literateModuleComment) {
        super(literateModuleComment);
        value = literateModuleComment.value;
        lcType = literateModuleComment.lcType;
    }

    public LiterateModuleComment(String value, LiterateCommentType lcType) {
        this.value = value;
        this.lcType = lcType;
    }

    public LiterateModuleComment(LiterateDefinitionComment ldc) {
        setSource(ldc.getSource());
        setLocation(ldc.getLocation());
        value = ldc.getValue();
        lcType = ldc.getType();
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    @Override
    public LiterateCommentType getType() {
        return lcType;
    }

    public void setValue(String value) {
        this.value = value;
    }

    public String getValue() {
        return value;
    }

    @Override
    public LiterateModuleComment shallowCopy() {
        return new LiterateModuleComment(this);
    }

    @Override
    public String toString() {
        return "/*"+lcType+value+"*/";
    }
}
