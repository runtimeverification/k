package org.kframework.backend.unparser;

public class Indenter {
	String endl = System.getProperty("line.separator");
	protected java.util.Stack<Integer> indents;
	protected java.lang.StringBuilder stringBuilder;
	protected boolean atBOL = true;
	protected IndentationOptions indentationOptions;

	public Indenter() {
		indents = new java.util.Stack<Integer>();
		stringBuilder = new java.lang.StringBuilder();
		indentationOptions = new IndentationOptions();
	}

	public Indenter(IndentationOptions indentationOptions) {
		indents = new java.util.Stack<Integer>();
		stringBuilder = new java.lang.StringBuilder();
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
		if (atBOL) {
			for (int i = 0; i < indentSize(); ++i) {
				stringBuilder.append(" ");
			}
		}
		int indexEndLine = stringBuilder.lastIndexOf(endl);
		int indexEndString = stringBuilder.length();
		if (indexEndString - indexEndLine + string.length() > getWidth()) {
			stringBuilder.append(endl);
			for (int i = 0; i < indentSize() + getAuxTabSize(); ++i) {
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
		indents.push(indentationOptions.getTabSize() * size);
	}

	public void unindent() {
		indents.pop();
	}

	public String toString() {
		return stringBuilder.toString();
	}
}
