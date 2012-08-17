package ro.uaic.info.fmse.unparser;

import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.List;
import java.util.Properties;
import java.util.Random;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.Map.Entry;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.k.LiterateComment.LiterateCommentType;
import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.utils.strings.StringUtil;
import ro.uaic.info.fmse.visitors.BasicVisitor;
import java.awt.Color;
import java.io.FileInputStream;
import java.io.IOException;

public class Indenter {
    String endl = System.getProperty("line.separator");
    protected java.util.Stack<Integer> indents;
    protected java.lang.StringBuilder stringBuilder;
    protected boolean atBOL = true;

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
