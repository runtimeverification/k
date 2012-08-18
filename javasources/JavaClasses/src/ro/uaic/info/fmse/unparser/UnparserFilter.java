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
import java.util.Stack;
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
    PriorityVisitor priorityVisitor = new PriorityVisitor();
    private Indenter result = new Indenter();
    private boolean firstPriorityBlock = false;
    private boolean firstProduction = false;
    private boolean inConfiguration = false;
    private static int TAB = 4;
    private java.util.List<String> variableList =
	new java.util.LinkedList<String>();
    private java.util.Map<Production, Integer> priorities = null;
    private java.util.Stack<ASTNode> stack = new java.util.Stack<ASTNode>();
    
    public UnparserFilter() {
    }
    
    public String getResult() {
	return result.toString();
    }
    
    @Override
    public void visit(Definition def) {
	prepare(def);
	def.accept(priorityVisitor);
	super.visit(def);
	postpare();
    }
    
    @Override
    public void visit(Import imp) {
	prepare(imp);
	result.write("imports " + imp.getName());
	result.endLine();
	postpare();
    }

    @Override
    public void visit(Module mod) {
	prepare(mod);
	if (!mod.isPredefined()) {
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
	postpare();
    }
    
    @Override
    public void visit(Syntax syn) {
	prepare(syn);
	firstPriorityBlock = true;
	result.write("syntax " + syn.getSort().getSort());
	result.indentToCurrent();
	for (PriorityBlock pb : syn.getPriorityBlocks()) {
	    pb.accept(this);
	}
	result.unindent();
	result.endLine();
	postpare();
    }

    @Override
    public void visit(PriorityBlock priorityBlock) {
	prepare(priorityBlock);
	if (firstPriorityBlock) {
	    result.write(" ::=");
	} else {
	    result.write("  >");
	}
	firstPriorityBlock = false;
	firstProduction = true;
	super.visit(priorityBlock);
	postpare();
    }

    @Override
    public void visit(Production prod) {
	prepare(prod);
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
	postpare();
    }

    @Override
    public void visit(Sort sort) {
	prepare(sort);
	result.write(sort.getSort());
	super.visit(sort);
	postpare();
    }

    @Override
    public void visit(Terminal terminal) {
	prepare(terminal);
	result.write("\"" + terminal.getTerminal() + "\"");
	super.visit(terminal);
	postpare();
    }

    @Override
    public void visit(UserList userList) {
	prepare(userList);
	result.write("List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}");
	super.visit(userList);
	postpare();
    }

    @Override
    public void visit(ListOfK listOfK) {
	prepare(listOfK);
	java.util.List<Term> termList = listOfK.getContents();
	for (int i = 0; i < termList.size(); ++i) {
	    termList.get(i).accept(this);
	    if (i != termList.size() - 1) {
		result.write(",, ");
	    }
	}
	super.visit(listOfK);
	postpare();
    }

    @Override
    public void visit(Attributes attributes) {
	prepare(attributes);
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
	postpare();
    }

    @Override
    public void visit(Attribute attribute) {
	prepare(attribute);
	result.write(attribute.getKey());
	if (!attribute.getValue().equals("")) {
	    result.write("(" + attribute.getValue() + ")");
	}
	postpare();
    }

    @Override
    public void visit(Configuration configuration) {
	prepare(configuration);
	result.write("configuration");
	result.endLine();
	result.indent(TAB);
	inConfiguration = true;
	configuration.getBody().accept(this);
	inConfiguration = false;
	result.unindent();
	result.endLine();
	result.endLine();
	postpare();
    }

    @Override
    public void visit(Cell cell) {
	prepare(cell);
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
	postpare();
    }

    @Override
    public void visit(Variable variable) {
	prepare(variable);
	result.write(variable.getName());
	if (!variableList.contains(variable.getName())) {
	    result.write(":" + variable.getSort());
	    variableList.add(variable.getName());
	}
	postpare();
    }

    @Override
    public void visit(Empty empty) {
	prepare(empty);
	result.write("." + empty.getSort());
	postpare();
    }

    @Override
    public void visit(Rule rule) {
	prepare(rule);
	result.write("rule ");
	if (!rule.getLabel().equals("")) {
	    result.write("[" + rule.getLabel() + "]: ");
	}
	variableList.clear();
	rule.getBody().accept(this);
	if (rule.getCondition() != null) {
	    result.write(" when ");
	    rule.getCondition().accept(this);
	}
	rule.getAttributes().accept(this);
	result.endLine();
	result.endLine();
	postpare();
    }

    @Override
    public void visit(KApp kapp) {
	prepare(kapp);
	kapp.getLabel().accept(this);
	result.write("(");
	kapp.getChild().accept(this);
	result.write(")");
	postpare();
    }

    @Override
    public void visit(KSequence ksequence) {
	prepare(ksequence);
	java.util.List<Term> contents = ksequence.getContents();
	for (int i = 0; i < contents.size(); i++) {
	    contents.get(i).accept(this);
	    if (i != contents.size() - 1) {
		result.write(" ~> ");
	    }
	}
	postpare();
    }

    @Override
    public void visit(TermCons termCons) {
	prepare(termCons);
	Production production = termCons.getProduction();
	if (production.isListDecl()) {
	    UserList userList = (UserList)production.getItems().get(0);
	    String separator = userList.getSeparator();
	    java.util.List<Term> contents = termCons.getContents();
	    for (int i = 0; i < contents.size(); ++i) {
		contents.get(i).accept(this);
		if (i != contents.size() - 1) {
		    result.write(separator + " ");
		}
	    }
	} else {
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
	postpare();
    }

    @Override
    public void visit(Rewrite rewrite) {
	prepare(rewrite);
	rewrite.getLeft().accept(this);
	result.write(" => ");
	rewrite.getRight().accept(this);
	postpare();
    }

    @Override
    public void visit(Constant constant) {
	prepare(constant);
	result.write(constant.getValue());
	postpare();
    }

    @Override
    public void visit(Collection collection) {
	prepare(collection);
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
	postpare();
    }

    @Override
    public void visit(CollectionItem collectionItem) {
	prepare(collectionItem);
	result.endLine();
	result.write("Don't know how to pretty print CollectionItem");
	result.endLine();
	super.visit(collectionItem);
	postpare();
    }

    @Override
    public void visit(BagItem bagItem) {
	prepare(bagItem);
	result.endLine();
	result.write("Don't know how to pretty print BagItem");
	result.endLine();
	super.visit(bagItem);
	postpare();
    }

    @Override
    public void visit(ListItem listItem) {
	prepare(listItem);
	result.endLine();
	result.write("Don't know how to pretty print ListItem");
	result.endLine();
	super.visit(listItem);
	postpare();
    }

    @Override
    public void visit(SetItem setItem) {
	prepare(setItem);
	result.endLine();
	result.write("Don't know how to pretty print ListItem");
	result.endLine();
	super.visit(setItem);
	postpare();
    }

    @Override
    public void visit(MapItem mapItem) {
	prepare(mapItem);
	mapItem.getKey().accept(this);
	result.write(" |-> ");
	mapItem.getValue().accept(this);
	postpare();
    }

    @Override
    public void visit(Hole hole) {
	prepare(hole);
	result.endLine();
	result.write("Don't know how to pretty print Hole");
	result.endLine();
	super.visit(hole);
	postpare();
    }

    public void visit(KInjectedLabel kInjectedLabel) {
	prepare(kInjectedLabel);
	result.endLine();
	result.write("Don't know how to pretty print KInjectedLabel");
	result.endLine();
	super.visit(kInjectedLabel);
	postpare();
    }

    @Override
    public void visit(KLabel kLabel) {
	prepare(kLabel);
	result.endLine();
	result.write("Don't know how to pretty print KLabel");
	result.endLine();
	super.visit(kLabel);
	postpare();
    }

    @Override
    public void visit(TermComment termComment) {
	prepare(termComment);
	result.endLine();
	result.write("Don't know how to pretty print TermComment");
	result.endLine();
	super.visit(termComment);
	postpare();
    }

    @Override
    public void visit(ro.uaic.info.fmse.k.List list) {
	prepare(list);
	result.endLine();
	result.write("Don't know how to pretty print List");
	result.endLine();
	super.visit(list);
	postpare();
    }

    @Override
    public void visit(ro.uaic.info.fmse.k.Map map) {
	prepare(map);
	java.util.List<Term> termList = map.getContents();
	for (int i = 0; i < termList.size(); ++i) {
	    termList.get(i).accept(this);
	    if (i != termList.size() - 1) {
		result.write(" ");
	    }
	}
	postpare();
    }

    @Override
    public void visit(Bag bag) {
	prepare(bag);
	java.util.List<Term> termList = bag.getContents();
	for (int i = 0; i < termList.size(); ++i) {
	    termList.get(i).accept(this);
	    if (i != termList.size() - 1) {
		result.write(" ");
	    }
	}
	postpare();
    }

    @Override
    public void visit(ro.uaic.info.fmse.k.Set set) {
	prepare(set);
	result.endLine();
	result.write("Don't know how to pretty print Set");
	result.endLine();
	super.visit(set);
	postpare();
    }

    @Override
    public void visit(ro.uaic.info.fmse.k.Ambiguity ambiguity) {
	prepare(ambiguity);
	result.endLine();
	result.write("Don't know how to pretty print Ambiguity");
	result.endLine();
	super.visit(ambiguity);
	postpare();
    }

    @Override
    public void visit(ro.uaic.info.fmse.k.Context context) {
	prepare(context);
	result.endLine();
	result.write("Don't know how to pretty print Ambiguity");
	result.endLine();
	super.visit(context);
	postpare();
    }

    public void visit(ro.uaic.info.fmse.k.Require require) {
	prepare(require);
	result.endLine();
	result.write("Don't know how to pretty print Require");
	result.endLine();
	super.visit(require);
	postpare();
    }

    private void prepare(ASTNode astNode) {
	if (!stack.empty()) {
	    if (needsParanthesis(stack.peek(), astNode)) {
		result.write("(");
	    }
	}
	stack.push(astNode);
    }

    private void postpare() {
	ASTNode astNode = stack.pop();
	if (!stack.empty()) {
	    if (needsParanthesis(stack.peek(), astNode)) {
		result.write(")");
	    }
	}
    }

    private boolean needsParanthesis(ASTNode upper, ASTNode astNode) {
	if (astNode instanceof Rewrite) {
	    if ((upper instanceof Cell) || (upper instanceof Rule)) {
		return false;
	    }
	    return true;
	} else if ((astNode instanceof TermCons) && (upper instanceof TermCons)) {
	    TermCons termConsNext = (TermCons)astNode;
	    TermCons termCons = (TermCons)upper;
	    Production productionNext = termConsNext.getProduction();
	    Production production = termCons.getProduction();
	    return !priorityVisitor.before(productionNext, production);
	} else {
	    return false;
	}
    }
}
