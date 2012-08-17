package ro.uaic.info.fmse.unparser;

import java.util.LinkedList;
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

public class UnparserFilter extends BasicVisitor {
    private Indenter result = new Indenter();
    private boolean firstPriorityBlock = false;
    private boolean firstProduction = false;
    private boolean inConfiguration = false;
    private static int TAB = 4;
    
    public UnparserFilter() {
    }
    
    public String getResult() {
	return result.toString();
    }
    
    @Override
    public void visit(Definition def) {
	super.visit(def);
    }
    
    @Override
    public void visit(Module mod) {
	if (mod.isPredefined())
	    return;
	result.write("module " + mod.getName());
	result.endLine();
	result.endLine();
	result.indent(TAB);
	super.visit(mod);
	result.unindent();
	result.write("endmodule");
	result.endLine();
	result.endLine();
    }
    
    @Override
    public void visit(Syntax syn) {
	firstPriorityBlock = true;
	result.write("syntax " + syn.getSort().getSort());
	result.indentToCurrent();
	for (PriorityBlock pb : syn.getPriorityBlocks()) {
	    pb.accept(this);
	}
	result.unindent();
	result.endLine();
    }

    @Override
    public void visit(PriorityBlock priorityBlock) {
	if (firstPriorityBlock) {
	    result.write(" ::=");
	} else {
	    result.write("  >");
	}
	firstPriorityBlock = false;
	firstProduction = true;
	super.visit(priorityBlock);
    }

    @Override
    public void visit(Production prod) {
	if (firstProduction) {
	    result.write(" ");
	} else {
	    result.write("  | ");
	}
	firstProduction = false;
	for (int i = 0; i < prod.getItems().size(); ++i) {
	    ProductionItem pi = prod.getItems().get(i);
	    pi.accept(this);
	    if (i != prod.getItems().size() - 1) {
		result.write(" ");
	    }
	}
	prod.getAttributes().accept(this);
	result.endLine();
    }

    @Override
    public void visit(Sort sort) {
	result.write(sort.getSort());
    }

    @Override
    public void visit(Terminal terminal) {
	result.write("\"" + terminal.getTerminal() + "\"");
    }

    @Override
    public void visit(UserList userList) {
	result.write("List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}");
    }

    @Override
    public void visit(Attributes attributes) {
	java.util.List<String> reject = new LinkedList<String>();
	reject.add("cons");
	reject.add("kgeneratedlabel");
	reject.add("prefixlabel");

	List<Attribute> attributeList = new LinkedList<Attribute>();
	List<Attribute> oldAttributeList = attributes.getContents();
	for (int i = 0; i < oldAttributeList.size(); ++i) {
	    if (!reject.contains(oldAttributeList.get(i).getKey())) {
		attributeList.add(oldAttributeList.get(i));
	    }
	}

	if (!attributeList.isEmpty()) {
	    result.write(" ");
	    result.write("[");
	    for (int i = 0; i < attributeList.size(); ++i) {
		attributeList.get(i).accept(this);
		if (i != attributeList.size() - 1) {
		    result.write(", ");
		}
	    }
	    result.write("]");
	}
    }

    @Override
    public void visit(Attribute attribute) {
	result.write(attribute.getKey());
	if (!attribute.getValue().equals("")) {
	    result.write("(" + attribute.getValue() + ")");
	}
    }

    @Override
    public void visit(Configuration configuration) {
	result.write("configuration");
	result.endLine();
	result.indent(TAB);
	inConfiguration = true;
	configuration.getBody().accept(this);
	inConfiguration = false;
	result.unindent();
	result.endLine();
	result.endLine();
    }

    @Override
    public void visit(Cell cell) {
	String attributes = "";
	for (Entry<String, String> entry : cell.getAttributes().entrySet()) {
	    if (entry.getKey() != "ellipses") {
		attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";
	    }
	}
	result.write("<" + cell.getLabel() + attributes + ">");
	if (inConfiguration) {
	    result.endLine();
	    result.indent(TAB);
	} else {
	    result.write(" ");
	}
	if (cell.hasLeftEllipsis()) {
	    result.write("... ");
	}
	cell.getContents().accept(this);
	if (cell.hasRightEllipsis()) {
	    result.write(" ...");
	}
	if (inConfiguration) {
	    result.endLine();
	    result.unindent();
	} else {
	    result.write(" ");
	}
	result.write("</" + cell.getLabel() + ">");
    }

    @Override
    public void visit(Variable variable) {
	result.write(variable.getName() + ":" + variable.getSort());
    }

    @Override
    public void visit(Empty empty) {
	result.write("." + empty.getSort());
    }

    @Override
    public void visit(Rule rule) {
	result.write("rule ");
	if (!rule.getLabel().equals("")) {
	    result.write("[" + rule.getLabel() + "]: ");
	}
	rule.getBody().accept(this);
	if (rule.getCondition() != null) {
	    result.write(" when ");
	    rule.getCondition().accept(this);
	}
	rule.getAttributes().accept(this);
	result.endLine();
	result.endLine();
    }

    @Override
    public void visit(KApp kapp) {
	kapp.getLabel().accept(this);
	result.write("(");
	kapp.getChild().accept(this);
	result.write(")");
    }

    @Override
    public void visit(KSequence ksequence) {
	java.util.List<Term> contents = ksequence.getContents();
	for (int i = 0; i < contents.size(); i++) {
	    contents.get(i).accept(this);
	    if (i != contents.size() - 1) {
		result.write(" ~> ");
	    }
	}
    }

    @Override
    public void visit(TermCons termCons) {
	Production production = termCons.getProduction();
	int where = 0;
	for (int i = 0; i < production.getItems().size(); ++i) {
	    ProductionItem productionItem = production.getItems().get(i);
	    if (productionItem.getType() != ProductionType.TERMINAL) {
		termCons.getContents().get(where++).accept(this);
	    } else {
		result.write(((Terminal)productionItem).getTerminal());
	    }
	    if (i != production.getItems().size() - 1) {
		result.write(" ");
	    }
	}
    }

    @Override
    public void visit(Rewrite rewrite) {
	rewrite.getLeft().accept(this);
	result.write(" => ");
	rewrite.getRight().accept(this);
    }

    @Override
    public void visit(Constant constant) {
	result.write(constant.getValue());
    }

    @Override
    public void visit(MapItem mapItem) {
	mapItem.getKey().accept(this);
	result.write(" |-> ");
	mapItem.getValue().accept(this);
    }

    @Override
    public void visit(Collection collection) {
	java.util.List<Term> contents = collection.getContents();
	for (int i = 0; i < contents.size(); ++i) {
	    contents.get(i).accept(this);
	    if (i != contents.size() - 1) {
		if (inConfiguration) {
		    result.endLine();
		} else {
		    result.write(" ");
		}
	    }
	}
    }
}
