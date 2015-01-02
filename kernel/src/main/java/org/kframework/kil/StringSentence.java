// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil;

import org.kframework.kil.visitors.Visitor;

/**
 * Used as a container for unparsed sentences like rule, context and configuration.
 *
 * @author Radu
 *
 */
public class StringSentence extends ModuleItem {
    private String content;
    private int contentStartLine;
    private int contentStartColumn;
    private String label;
    private String type;

    public StringSentence(String content, int contentStartLine, int contentStartColumn, String type, String label) {
        this.content = content;
        this.contentStartLine = contentStartLine;
        this.contentStartColumn = contentStartColumn;
        this.type = type;
        this.label = label;
    }

    public StringSentence(StringSentence node) {
        super(node);
        this.content = node.content;
    }

    public String toString() {
        return type+"["+label+"]:"+content;
    }

    @Override
    protected <P, R, E extends Throwable> R accept(Visitor<P, R, E> visitor, P p) throws E {
        return visitor.complete(this, visitor.visit(this, p));
    }

    public String getContent() {
        return content;
    }

    public void setContent(String content) {
        this.content = content;
    }

    @Override
    public StringSentence shallowCopy() {
        return new StringSentence(this);
    }

    public void setType(String type) {
        this.type = type;
    }

    public String getType() {
        return type;
    }

    public String getLabel() {
        return label;
    }

    public void setLabel(String label) {
        this.label = label;
    }

    public int getContentStartLine() {
        return contentStartLine;
    }

    public int getContentStartColumn() {
        return contentStartColumn;
    }
}
