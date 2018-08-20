// Copyright (c) 2016-2018 K Team. All Rights Reserved.

package org.kframework.unparser;

public class Indenter implements Appendable {
    private final int indentSize;
    private int indentationLevel = 0;
    private boolean atNewLine = true;
    private final StringBuilder sb = new StringBuilder();

    public Indenter(int indentSize) {
        this.indentSize = indentSize;
    }

    public Indenter append(CharSequence str) {
        printIndent();
        sb.append(str);
        return this;
    }

    public Indenter append(CharSequence str, int start, int end) {
        printIndent();
        sb.append(str, start, end);
        return this;
    }

    private void printIndent() {
        if (atNewLine) {
            for (int i = 0; i < indentSize * indentationLevel; i++) {
                sb.append(" ");
            }
            atNewLine = false;
        }
    }

    public Indenter indent() {
        indentationLevel++;
        return this;
    }

    public Indenter dedent() {
        indentationLevel--;
        return this;
    }

    public Indenter newline() {
        sb.append(System.getProperty("line.separator"));
        atNewLine = true;
        return this;
    }

    @Override
    public String toString() {
        return sb.toString();
    }

    public Indenter append(char c) {
        printIndent();
        sb.append(c);
        return this;
    }
}
