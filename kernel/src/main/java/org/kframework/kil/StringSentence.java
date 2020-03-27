// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.kil;

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

    @Override
    public void toString(StringBuilder sb) {
        switch(type) {
        case "config":
          sb.append("  configuration ");
          break;
        case "alias":
          sb.append("  context alias ");
          break;
        default:
          sb.append("  ").append(type).append(" ");
          break;
        }
        if (!label.equals("")) {
          sb.append("[").append(label).append("]: ");
        }
        sb.append(content).append(" ").append(getAttributes());
    }

    public String getContent() {
        return content;
    }

    public void setContent(String content) {
        this.content = content;
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
