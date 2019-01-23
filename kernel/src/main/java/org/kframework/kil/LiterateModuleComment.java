// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

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
