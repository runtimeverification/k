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

public class UnparserFilter extends BasicVisitor {
    String endl = System.getProperty("line.separator");
    private String result = "";
    private boolean firstPriorityBlock = false;
    private boolean firstProduction = false;
    private boolean inConfiguration = false;
    
    public UnparserFilter() {
    }
    
    public String getResult() {
	return result;
    }
    
    @Override
    public void visit(Definition def) {
	super.visit(def);
    }
    
    @Override
    public void visit(Module mod) {
	if (mod.isPredefined())
	    return;
	result += "module " + mod.getName() + endl + endl;
	super.visit(mod);
	result += "endmodule" + endl + endl;
    }
    
    @Override
    public void visit(Syntax syn) {
	firstPriorityBlock = true;
	result += "syntax " + syn.getSort().getSort();
	for (PriorityBlock pb : syn.getPriorityBlocks()) {
	    pb.accept(this);
	}
	result += endl;
    }

    @Override
    public void visit(PriorityBlock priorityBlock) {
	if (firstPriorityBlock) {
	    result += " ::=";
	} else {
	    result += " >";
	}
	firstPriorityBlock = false;
	firstProduction = true;
	super.visit(priorityBlock);
    }

    @Override
    public void visit(Production prod) {
	if (firstProduction) {
	    result += " ";
	} else {
	    result += " | ";
	}
	firstProduction = false;
	for (int i = 0; i < prod.getItems().size(); ++i) {
	    ProductionItem pi = prod.getItems().get(i);
	    pi.accept(this);
	    if (i != prod.getItems().size() - 1) {
		result += " ";
	    }
	}
	prod.getAttributes().accept(this);
	result += endl;
    }

    @Override
    public void visit(Sort sort) {
	result += sort.getSort();
    }

    @Override
    public void visit(Terminal terminal) {
	result += "\"" + terminal.getTerminal() + "\"";
    }

    @Override
    public void visit(UserList userList) {
	result += "List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}";
    }

    @Override
    public void visit(Attributes attributes) {
	if (!attributes.isEmpty()) {
	    result += " ";
	    result += "[";
	    List<Attribute> attributeList = attributes.getContents();
	    for (int i = 0; i < attributeList.size(); ++i) {
		attributeList.get(i).accept(this);
		if (i != attributeList.size() - 1) {
		    result += ", ";
		}
	    }
	    result += "]";
	}
    }

    @Override
    public void visit(Attribute attribute) {
	result += attribute.getKey();
	if (!attribute.getValue().equals("")) {
	    result += "(" + attribute.getValue() + ")";
	}
    }

    @Override
    public void visit(Configuration configuration) {
	result += "configuration" + endl;
	inConfiguration = true;
	configuration.getBody().accept(this);
	inConfiguration = false;
	result += endl + endl;
    }

    @Override
    public void visit(Cell cell) {
	String attributes = "";
	for (Entry<String, String> entry : cell.getAttributes().entrySet()) {
	    if (entry.getKey() != "ellipses") {
		attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";
	    }
	}
	result += "<" + cell.getLabel() + attributes + "> ";
	if (inConfiguration) {
	    result += endl;
	}
	if (cell.hasLeftEllipsis()) {
	    result += "... ";
	}
	cell.getContents().accept(this);
	if (cell.hasRightEllipsis()) {
	    result += " ...";
	}
	if (inConfiguration) {
	    result += endl;
	}
	result += "</" + cell.getLabel() + ">";
    }

    @Override
    public void visit(Variable variable) {
	result += variable.getName() + ":" + variable.getSort();
    }

    @Override
    public void visit(Empty empty) {
	result += "." + empty.getSort();
    }

    @Override
    public void visit(Rule rule) {
	result += "rule ";
	if (!rule.getLabel().equals("")) {
	    result += "[" + rule.getLabel() + "]: ";
	}
	rule.getBody().accept(this);
	if (rule.getCondition() != null) {
	    result += "when ";
	    rule.getCondition().accept(this);
	}
	rule.getAttributes().accept(this);
	result += endl;
	result += endl;
    }

    @Override
    public void visit(KApp kapp) {
	kapp.getLabel().accept(this);
	result += "(";
	kapp.getChild().accept(this);
	result += ")";
    }

    @Override
    public void visit(KSequence ksequence) {
	java.util.List<Term> contents = ksequence.getContents();
	for (int i = 0; i < contents.size(); i++) {
	    contents.get(i).accept(this);
	    if (i != contents.size() - 1) {
		result += " ~> ";
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
		result += ((Terminal)productionItem).getTerminal();
	    }
	    result += " ";
	}
    }

    @Override
    public void visit(Rewrite rewrite) {
	rewrite.getLeft().accept(this);
	result += " => ";
	rewrite.getRight().accept(this);
    }

    @Override
    public void visit(Constant constant) {
	result += constant.getValue();
    }

    @Override
    public void visit(MapItem mapItem) {
	mapItem.getKey().accept(this);
	result += " |-> ";
	mapItem.getValue().accept(this);
    }

    @Override
    public void visit(Collection collection) {
	java.util.List<Term> contents = collection.getContents();
	for (int i = 0; i < contents.size(); ++i) {
	    contents.get(i).accept(this);
	    if (i != contents.size()) {
		result += " ";
	    }
	}
    }
}
