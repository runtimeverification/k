// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

public class Indenter {
    String endl = System.getProperty("line.separator");
    protected java.util.Stack<Integer> indents;
    protected java.lang.StringBuilder stringBuilder;
    protected boolean atBOL = true;
    protected IndentationOptions indentationOptions;
    private int lineNo;
    private int colNo;

    public Indenter() {
        this(new IndentationOptions());
    }

    public Indenter(IndentationOptions indentationOptions) {
        indents = new java.util.Stack<Integer>();
        stringBuilder = new java.lang.StringBuilder();
        lineNo = 1;
        colNo = 1;
        this.indentationOptions = indentationOptions;
    }

    private int indentSize() {
        int size = 0;
        for (Integer i : indents) {
            size += i;
        }
        return size;
    }

    public void setWidth(int newWidth) {
        indentationOptions.setWidth(newWidth);
    }

    public int getWidth() {
        return indentationOptions.getWidth();
    }

    public int getAuxTabSize() {
        return indentationOptions.getAuxTabSize();
    }

    public void write(String string) {
        if (string.isEmpty()) {
            return;
        }
//        System.err.println("@" + string + "@"); // for debugging
        if (atBOL) {
            for (int i = 0; i < indentSize(); ++i) {
                stringBuilder.append(" ");
                colNo++;
            }
        }
        int indexEndLine = stringBuilder.lastIndexOf(endl) + endl.length();
        int indexEndString = stringBuilder.length();
        if (indexEndString - indexEndLine + string.length() > getWidth() && getWidth() >= 0) {
            stringBuilder.append(endl);
            lineNo++;
            colNo = 1;
            for (int i = 0; i < indentSize() + getAuxTabSize(); ++i) {
                stringBuilder.append(" ");
                colNo++;
            }
        }
        stringBuilder.append(string);
        colNo += string.length();
        atBOL = false;
    }

    public void endLine() {
        atBOL = true;
        stringBuilder.append(endl);
        lineNo++;
        colNo = 1;
    }

    public void indentToCurrent() {
        int indexEndLine = stringBuilder.lastIndexOf(endl);
        int indexEndString = stringBuilder.length();
        indents.push(indexEndString - indexEndLine - indentSize());
    }

    public void indent(int size) {
        indents.push(indentationOptions.getTabSize() * size);
    }

    public void unindent() {
        indents.pop();
    }

    public StringBuilder getResult() {
        return stringBuilder;
    }

    public String toString() {
        return stringBuilder.toString();
    }

    public int getLineNo() {
        return lineNo;
    }

    public int getColNo() {
        return colNo;
    }
}
