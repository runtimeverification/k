package org.kframework.unparser;


public class Indenter {
    String endl = System.getProperty("line.separator");
    protected java.util.Stack<Integer> indents;
    protected java.lang.StringBuilder stringBuilder;
    protected boolean atBOL = true;
    private static int width = 78;
    private static int auxIndent = 2;

    public Indenter() {
	indents = new java.util.Stack<Integer>();
	stringBuilder = new java.lang.StringBuilder();
    }

    private int indentSize() {
	int size = 0;
	for (Integer i : indents) {
	    size += i;
	}
	return size;
    }

    public void write(String string) {
	if (atBOL) {
	    for (int i = 0; i < indentSize(); ++i) {
		stringBuilder.append(" ");
	    }
	}
	int indexEndLine = stringBuilder.lastIndexOf(endl);
	int indexEndString = stringBuilder.length();
	if (indexEndString - indexEndLine + string.length() > width) {
	    stringBuilder.append(endl);
	    for (int i = 0; i < indentSize() + auxIndent; ++i) {
		stringBuilder.append(" ");
	    }
	}
	stringBuilder.append(string);
	atBOL = false;
    }

    public void endLine() {
	atBOL = true;
	stringBuilder.append(endl);
    }

    public void indentToCurrent() {
	int indexEndLine = stringBuilder.lastIndexOf(endl);
	int indexEndString = stringBuilder.length();
	indents.push(indexEndString - indexEndLine - indentSize());
    }

    public void indent(int size) {
	indents.push(size);
    }

    public void unindent() {
	indents.pop();
    }

    public String toString() {
	return stringBuilder.toString();
    }
}
