package org.kframework.krun.gui.Controller;

import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import org.apache.commons.lang3.StringEscapeUtils;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListItem;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.MapItem;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Require;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.Token;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;

public class XmlUnparseFilter extends BasicVisitor {

    private StringBuffer buffer = new StringBuffer();
    private boolean firstPriorityBlock = false;
    private boolean firstProduction = false;
    private boolean inConfiguration = false;
    private boolean addParentheses;
    private int inTerm = 0;
    private boolean forEquivalence = false;
    private java.util.List<String> variableList = new java.util.LinkedList<String>();
    private java.util.Stack<ASTNode> stack = new java.util.Stack<ASTNode>();

    public XmlUnparseFilter(boolean inConfiguration, boolean addParentheses, org.kframework.kil.loader.Context context) {
        super(context);
        this.inConfiguration = inConfiguration;
        this.inTerm = 0;
        this.addParentheses = addParentheses;
    }

    public void setForEquivalence() {
        forEquivalence = true;
    }
    
    public String getResult() {

        return buffer.toString();
    }

    @Override
    public void visit(Definition def) {

        prepare(def);
        super.visit(def);
        postpare();
    }

    @Override
    public void visit(Import imp) {

        prepare(imp);
        if (!forEquivalence) {
            buffer.append("imports " + StringEscapeUtils.escapeXml(imp.getName()));

            buffer.append("\n");
        }
        postpare();
    }

    @Override
    public void visit(Module mod) {

        prepare(mod);
        if (!mod.isPredefined()) {
            if (!forEquivalence) {
                buffer.append("module " + StringEscapeUtils.escapeXml(mod.getName()));
                buffer.append("\n");
                buffer.append("\n");
            }
            super.visit(mod);
            if (!forEquivalence) {
                buffer.append("endmodule");
                buffer.append("\n");
                buffer.append("\n");
            }
        }
        postpare();
    }

    @Override
    public void visit(Syntax syn) {

        prepare(syn);
        firstPriorityBlock = true;
        buffer.append("syntax " + StringEscapeUtils.escapeXml(syn.getSort().getName()));
        if (syn.getPriorityBlocks() != null)
            for (PriorityBlock pb : syn.getPriorityBlocks()) {
                pb.accept(this);
            }
        buffer.append("\n");
        postpare();
    }

    @Override
    public void visit(PriorityBlock priorityBlock) {

        prepare(priorityBlock);
        if (firstPriorityBlock) {
            buffer.append(" ::=");
        } else {
            buffer.append(StringEscapeUtils.escapeXml("  >"));
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
            buffer.append(" ");
        } else {
            buffer.append("  | ");
        }
        firstProduction = false;
        for (int i = 0; i < prod.getItems().size(); ++i) {
            ProductionItem pi = prod.getItems().get(i);
            pi.accept(this);
            if (i != prod.getItems().size() - 1) {
                buffer.append(" ");
            }
        }
        prod.getAttributes().accept(this);
        buffer.append("\n");
        postpare();
    }

    @Override
    public void visit(Sort sort) {

        prepare(sort);
        buffer.append(StringEscapeUtils.escapeXml(sort.getName()));
        super.visit(sort);
        postpare();
    }

    @Override
    public void visit(Terminal terminal) {

        prepare(terminal);
        buffer.append(StringEscapeUtils.escapeXml ("\"" + terminal.getTerminal() + "\""));
        super.visit(terminal);
        postpare();
    }

    @Override
    public void visit(UserList userList) {

        prepare(userList);
        buffer.append(StringEscapeUtils.escapeXml("List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}"));
        super.visit(userList);
        postpare();
    }

    @Override
    public void visit(KList listOfK) {

        prepare(listOfK);
        java.util.List<Term> termList = listOfK.getContents();
        for (int i = 0; i < termList.size(); ++i) {
            termList.get(i).accept(this);
            if (i != termList.size() - 1) {
                buffer.append(",, ");
            }
        }
        if (termList.size() == 0) {
            buffer.append(".KList");
        }
        postpare();
    }

    @Override
    public void visit(Attributes attributes) {

        prepare(attributes);
        java.util.List<String> reject = new LinkedList<String>();
        reject.add("cons");
        reject.add("kgeneratedlabel");
        reject.add("prefixlabel");
        reject.add("filename");
        reject.add("location");

        List<Attribute> attributeList = new LinkedList<Attribute>();
        List<Attribute> oldAttributeList = attributes.getContents();
        for (int i = 0; i < oldAttributeList.size(); ++i) {
            if (!reject.contains(oldAttributeList.get(i).getKey())) {
                attributeList.add(oldAttributeList.get(i));
            }
        }

        if (!attributeList.isEmpty()) {
            buffer.append(" ");
            buffer.append("[");
            for (int i = 0; i < attributeList.size(); ++i) {
                attributeList.get(i).accept(this);
                if (i != attributeList.size() - 1) {
                    buffer.append(", ");
                }
            }
            buffer.append("]");
        }
        postpare();
    }

    @Override
    public void visit(Attribute attribute) {

        prepare(attribute);
        buffer.append(StringEscapeUtils.escapeXml(attribute.getKey()));
        if (!attribute.getValue().equals("")) {
            buffer.append("(" + StringEscapeUtils.escapeXml(attribute.getValue()) + ")");
        }
        postpare();
    }

    @Override
    public void visit(Configuration configuration) {

        prepare(configuration);
        if (!forEquivalence) {
            buffer.append("configuration");
            buffer.append("\n");
            inConfiguration = true;
            configuration.getBody().accept(this);
            inConfiguration = false;
            buffer.append("\n");
            buffer.append("\n");
        }
        postpare();
    }

    @Override
    public void visit(Cell cell) {

        prepare(cell);
        String attributes = "";
        for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
            if (entry.getKey() != "ellipses") {
                attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";
            }
        }
        String colorCode = "";
        Cell declaredCell = context.cells.get(cell.getLabel());
        buffer.append("<" + cell.getLabel() + attributes + ">");
        if (inConfiguration && inTerm == 0) {
            buffer.append("\n");
        } else {
            if (cell.hasLeftEllipsis()) {
                buffer.append("... ");
            } else {
                buffer.append(" ");
            }
        }
        cell.getContents().accept(this);
        buffer.append(colorCode);
        if (inConfiguration && inTerm == 0) {
            buffer.append("\n");
        } else {
            if (cell.hasRightEllipsis()) {
                buffer.append(" ...");
            } else {
                buffer.append(" ");
            }
        }
        buffer.append("</" + cell.getLabel() + ">");
        postpare();
    }

    @Override
    public void visit(Variable variable) {

        prepare(variable);
        if (variable.isFresh())
            buffer.append("?");
        buffer.append(StringEscapeUtils.escapeXml(variable.getName()));
        if (!variableList.contains(variable.getName())) {
            buffer.append(":" + StringEscapeUtils.escapeXml(variable.getSort()));
            variableList.add(variable.getName());
        }
        postpare();
    }

    @Override
    public void visit(ListTerminator terminator) {

        prepare(terminator);
        buffer.append(StringEscapeUtils.escapeXml(terminator.toString()));
        postpare();
    }

    @Override
    public void visit(Rule rule) {
        prepare(rule);
        buffer.append("rule ");
        if (!"".equals(rule.getLabel())) {
            buffer.append("[" + StringEscapeUtils.escapeXml(rule.getLabel()) + "]: ");
        }
        variableList.clear();
        rule.getBody().accept(this);
        if (rule.getRequires() != null) {
            buffer.append(" when ");
            rule.getRequires().accept(this);
        }
        if (rule.getEnsures() != null) {
            buffer.append(" ensures ");
            rule.getEnsures().accept(this);
        }
        rule.getAttributes().accept(this);
        buffer.append("\n");
        buffer.append("\n");
        postpare();
    }

    @Override
    public void visit(KApp kapp) {

        prepare(kapp);
        Term child = kapp.getChild();
        Term label = kapp.getLabel();
        if (label instanceof Token) {
            assert child instanceof KList : "child of KApp with Token is not KList";
        assert ((KList) child).isEmpty() : "child of KApp with Token is not empty";
        buffer.append(StringEscapeUtils.escapeXml(((Token) label).value()));
        } else {
            label.accept(this);
            buffer.append("(");
            child.accept(this);
            buffer.append(")");
        }
        postpare();
    }

    @Override
    public void visit(KSequence ksequence) {

        prepare(ksequence);
        java.util.List<Term> contents = ksequence.getContents();
        if (!contents.isEmpty()) {
            for (int i = 0; i < contents.size(); i++) {
                contents.get(i).accept(this);
                if (i != contents.size() - 1) {
                    buffer.append(StringEscapeUtils.escapeXml(" ~> "));
                }
            }
        } else {
            buffer.append(".K");
        }
        postpare();
    }

    @Override
    public void visit(TermCons termCons) {

        prepare(termCons);
        inTerm++;
        Production production = termCons.getProduction();
        if (production.isListDecl()) {
            UserList userList = (UserList) production.getItems().get(0);
            String separator = userList.getSeparator();
            java.util.List<Term> contents = termCons.getContents();
            contents.get(0).accept(this);
            buffer.append(StringEscapeUtils.escapeXml(separator) + " ");
            contents.get(1).accept(this);
        } else {
            int where = 0;
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    termCons.getContents().get(where++).accept(this);
                } else {
                    buffer.append(StringEscapeUtils.escapeXml(((Terminal) productionItem).getTerminal()));
                }
                if (i != production.getItems().size() - 1) {
                    buffer.append(" ");
                }
            }
        }
        inTerm--;
        postpare();
    }

    @Override
    public void visit(Rewrite rewrite) {

        prepare(rewrite);
        rewrite.getLeft().accept(this);
        buffer.append(StringEscapeUtils.escapeXml(" => "));
        rewrite.getRight().accept(this);
        postpare();
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {

        prepare(kLabelConstant);
        buffer.append(StringEscapeUtils.escapeXml(kLabelConstant.getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)")));
        postpare();
    }

    @Override
    public void visit(Collection collection) {

        prepare(collection);
        java.util.List<Term> contents = collection.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            contents.get(i).accept(this);
            if (i != contents.size() - 1) {
                if (inConfiguration && inTerm == 0) {
                    buffer.append("\n");
                } else {
                    buffer.append(" ");
                }
            }
        }
        if (contents.size() == 0) {
            buffer.append("." + StringEscapeUtils.escapeXml(collection.getSort()));
        }
        postpare();
    }

    @Override
    public void visit(CollectionItem collectionItem) {

        prepare(collectionItem);
        super.visit(collectionItem);
        postpare();
    }

    @Override
    public void visit(BagItem bagItem) {

        prepare(bagItem);
        buffer.append("BagItem(");
        super.visit(bagItem);
        buffer.append(")");
        postpare();
    }

    @Override
    public void visit(ListItem listItem) {

        prepare(listItem);
        buffer.append("ListItem(");
        super.visit(listItem);
        buffer.append(")");
        postpare();
    }

    @Override
    public void visit(SetItem setItem) {

        prepare(setItem);
        buffer.append("SetItem(");
        super.visit(setItem);
        buffer.append(")");
        postpare();
    }

    @Override
    public void visit(MapItem mapItem) {

        prepare(mapItem);
        mapItem.getKey().accept(this);
        buffer.append(StringEscapeUtils.escapeXml(" |-> "));
        mapItem.getValue().accept(this);
        postpare();
    }

    @Override
    public void visit(Hole hole) {

        buffer.append("HOLE");
        postpare();
    }

    @Override
    public void visit(FreezerHole hole) {

        prepare(hole);
        buffer.append("HOLE(" + hole.getIndex() + ")");
        postpare();
    }

    @Override
    public void visit(Freezer freezer) {

        prepare(freezer);
        freezer.getTerm().accept(this);
        postpare();
    }

    @Override
    public void visit(KInjectedLabel kInjectedLabel) {

        prepare(kInjectedLabel);
        Term term = kInjectedLabel.getTerm();
        if (MetaK.isKSort(term.getSort())) {
            buffer.append(StringEscapeUtils.escapeXml(kInjectedLabel.getInjectedSort(term.getSort())));
            buffer.append("2KLabel ");
        } else {
            buffer.append("# ");
        }
        term.accept(this);
        postpare();
    }

    @Override
    public void visit(KLabel kLabel) {

        prepare(kLabel);
        buffer.append("\n");
        buffer.append("Don't know how to pretty print KLabel");
        buffer.append("\n");
        super.visit(kLabel);
        postpare();
    }

    @Override
    public void visit(TermComment termComment) {

        prepare(termComment);
        buffer.append("<br/>");
        super.visit(termComment);
        postpare();
    }

    @Override
    public void visit(org.kframework.kil.List list) {

        prepare(list);
        super.visit(list);
        postpare();
    }

    @Override
    public void visit(org.kframework.kil.Map map) {

        prepare(map);
        super.visit(map);
        postpare();
    }

    @Override
    public void visit(Bag bag) {

        prepare(bag);
        super.visit(bag);
        postpare();
    }

    @Override
    public void visit(org.kframework.kil.Set set) {

        prepare(set);
        super.visit(set);
        postpare();
    }

    @Override
    public void visit(org.kframework.kil.Ambiguity ambiguity) {

        prepare(ambiguity);
        buffer.append("amb(");
        buffer.append("\n");
        java.util.List<Term> contents = ambiguity.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            contents.get(i).accept(this);
            if (i != contents.size() - 1) {
                buffer.append(",");
                buffer.append("\n");
            }
        }
        buffer.append("\n");
        buffer.append(")");
        postpare();
    }

    @Override
    public void visit(org.kframework.kil.Context context) {

        prepare(context);
        buffer.append("context ");
        variableList.clear();
        context.getBody().accept(this);
        if (context.getRequires() != null) {
            buffer.append(" when ");
            context.getRequires().accept(this);
        }
        if (context.getEnsures() != null) {
            buffer.append(" ensures ");
            context.getEnsures().accept(this);
        }
        context.getAttributes().accept(this);
        buffer.append("\n");
        buffer.append("\n");
        postpare();
    }

    @Override
    public void visit(LiterateDefinitionComment literateDefinitionComment) {

        prepare(literateDefinitionComment);
        // buffer.append(literateDefinitionComment.getValue());
        // buffer.append("\n");
        postpare();
    }

    @Override
    public void visit(Require require) {

        prepare(require);
        if (!forEquivalence) {
            buffer.append("require \"" + StringEscapeUtils.escapeXml(require.getValue()) + "\"");
            buffer.append("\n");
        }
        postpare();
    }

    @Override
    public void visit(BackendTerm term) {

        prepare(term);
        buffer.append(StringEscapeUtils.escapeXml(term.getValue()));
        postpare();
    }

    @Override
    public void visit(Bracket br) {

        prepare(br);
        buffer.append("(");
        br.getContent().accept(this);
        buffer.append(")");
        postpare();
    }

    @Override
    public void visit(Cast c) {

        prepare(c);
        c.getContent().accept(this);
        buffer.append(" :");
        if (c.isSyntactic()) {
            buffer.append(":");
        }
        buffer.append(StringEscapeUtils.escapeXml(c.getSort()));
        postpare();
    }

    @Override
    public void visit(Token t) {

        prepare(t);
        buffer.append(StringEscapeUtils.escapeXml("#token(\"" + t.tokenSort() + "\", \"" + t.value() + "\")"));
        postpare();
    }

    private void prepare(ASTNode astNode) {

        if (!stack.empty()) {
            if (needsParanthesis(stack.peek(), astNode)) {
                buffer.append("(");
            }
        }
        stack.push(astNode);
    }

    private void postpare() {

        ASTNode astNode = stack.pop();
        if (!stack.empty()) {
            if (needsParanthesis(stack.peek(), astNode)) {
                buffer.append(")");
            }
        }
    }

    private boolean needsParanthesis(ASTNode upper, ASTNode astNode) {

        if (!addParentheses)
            return false;
        if (astNode instanceof Rewrite) {
            if ((upper instanceof Cell) || (upper instanceof Rule)) {
                return false;
            }
            return true;
        } else if ((astNode instanceof TermCons) && (upper instanceof TermCons)) {
            TermCons termConsNext = (TermCons) astNode;
            TermCons termCons = (TermCons) upper;
            Production productionNext = termConsNext.getProduction();
            Production production = termCons.getProduction();
            if (context.isPriorityWrong(production.getKLabel(), productionNext.getKLabel())) {
                return true;
            }
            return termConsNext.getContents().size() != 0;
        } else {
            return false;
        }
    }

    public void setInConfiguration(boolean inConfiguration) {
        this.inConfiguration = inConfiguration;
    }

}

