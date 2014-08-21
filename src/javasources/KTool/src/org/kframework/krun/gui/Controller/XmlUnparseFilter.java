// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.Controller;

import java.util.Iterator;
import java.util.Map.Entry;

import org.apache.commons.lang3.StringEscapeUtils;
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
import org.kframework.kil.ListTerminator;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Require;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.NonTerminal;
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

    public XmlUnparseFilter(boolean inConfiguration, boolean addParentheses,
            org.kframework.kil.loader.Context context) {
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
    public Void visit(Definition def, Void _) {

        prepare(def);
        super.visit(def, _);
        return postpare();
    }

    @Override
    public Void visit(Import imp, Void _) {

        prepare(imp);
        if (!forEquivalence) {
            buffer.append("imports "
                    + StringEscapeUtils.escapeXml(imp.getName()));

            buffer.append("\n");
        }
        return postpare();
    }

    @Override
    public Void visit(Module mod, Void _) {

        prepare(mod);
        if (!mod.isPredefined()) {
            if (!forEquivalence) {
                buffer.append("module "
                        + StringEscapeUtils.escapeXml(mod.getName()));
                buffer.append("\n");
                buffer.append("\n");
            }
            super.visit(mod, _);
            if (!forEquivalence) {
                buffer.append("endmodule");
                buffer.append("\n");
                buffer.append("\n");
            }
        }
        return postpare();
    }

    @Override
    public Void visit(Syntax syn, Void _) {

        prepare(syn);
        firstPriorityBlock = true;
        buffer.append("syntax "
                + StringEscapeUtils.escapeXml(syn.getDeclaredSort().getName()));
        if (syn.getPriorityBlocks() != null)
            for (PriorityBlock pb : syn.getPriorityBlocks()) {
                this.visitNode(pb);
            }
        buffer.append("\n");
        return postpare();
    }

    @Override
    public Void visit(PriorityBlock priorityBlock, Void _) {

        prepare(priorityBlock);
        if (firstPriorityBlock) {
            buffer.append(" ::=");
        } else {
            buffer.append(StringEscapeUtils.escapeXml("  >"));
        }
        firstPriorityBlock = false;
        firstProduction = true;
        super.visit(priorityBlock, _);
        return postpare();
    }

    @Override
    public Void visit(Production prod, Void _) {

        prepare(prod);
        if (firstProduction) {
            buffer.append(" ");
        } else {
            buffer.append("  | ");
        }
        firstProduction = false;
        for (int i = 0; i < prod.getItems().size(); ++i) {
            ProductionItem pi = prod.getItems().get(i);
            this.visitNode(pi);
            if (i != prod.getItems().size() - 1) {
                buffer.append(" ");
            }
        }
        this.visitNode(prod.getAttributes());
        buffer.append("\n");
        return postpare();
    }

    @Override
    public Void visit(NonTerminal sort, Void _) {

        prepare(sort);
        buffer.append(StringEscapeUtils.escapeXml(sort.getName()));
        super.visit(sort, _);
        return postpare();
    }

    @Override
    public Void visit(Terminal terminal, Void _) {

        prepare(terminal);
        buffer.append(StringEscapeUtils.escapeXml("\"" + terminal.getTerminal()
                + "\""));
        super.visit(terminal, _);
        return postpare();
    }

    @Override
    public Void visit(UserList userList, Void _) {

        prepare(userList);
        buffer.append(StringEscapeUtils.escapeXml("List{" + userList.getSort()
                + ",\"" + userList.getSeparator() + "\"}"));
        super.visit(userList, _);
        return postpare();
    }

    @Override
    public Void visit(KList listOfK, Void _) {

        prepare(listOfK);
        java.util.List<Term> termList = listOfK.getContents();
        for (int i = 0; i < termList.size(); ++i) {
            this.visitNode(termList.get(i));
            if (i != termList.size() - 1) {
                buffer.append(",, ");
            }
        }
        if (termList.size() == 0) {
            buffer.append(".KList");
        }
        return postpare();
    }

    @Override
    public Void visit(Attributes attributes, Void _) {

        prepare(attributes);
        if (!attributes.isEmpty()) {
            buffer.append(" ");
            buffer.append("[");
            Iterator<Attribute<?>> iter = attributes.values().iterator();
            for (int i = 0; i < attributes.size(); ++i) {
                this.visitNode(iter.next());
                if (i != attributes.size() - 1) {
                    buffer.append(", ");
                }
            }
            buffer.append("]");
        }
        return postpare();
    }

    @Override
    public Void visit(Attribute attribute, Void _) {

        prepare(attribute);
        buffer.append(attribute.toString());
        return postpare();
    }

    @Override
    public Void visit(Configuration configuration, Void _) {

        prepare(configuration);
        if (!forEquivalence) {
            buffer.append("configuration");
            buffer.append("\n");
            inConfiguration = true;
            this.visitNode(configuration.getBody());
            inConfiguration = false;
            buffer.append("\n");
            buffer.append("\n");
        }
        return postpare();
    }

    @Override
    public Void visit(Cell cell, Void _) {

        prepare(cell);
        String attributes = "";
        for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
            if (entry.getKey() != "ellipses") {
                attributes += " " + entry.getKey() + "=\"" + entry.getValue()
                        + "\"";
            }
        }
        String colorCode = "";
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
        this.visitNode(cell.getContents());
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
        return postpare();
    }

    @Override
    public Void visit(Variable variable, Void _) {

        prepare(variable);
        if (variable.isFreshVariable())
            buffer.append("?");
        else if (variable.isFreshConstant())
            buffer.append("!");
        buffer.append(StringEscapeUtils.escapeXml(variable.getName()));
        if (!variableList.contains(variable.getName())) {
            buffer.append(":" + StringEscapeUtils.escapeXml(variable.getSort().getName()));
            variableList.add(variable.getName());
        }
        return postpare();
    }

    @Override
    public Void visit(ListTerminator terminator, Void _) {

        prepare(terminator);
        buffer.append(StringEscapeUtils.escapeXml(terminator.toString()));
        return postpare();
    }

    @Override
    public Void visit(Rule rule, Void _) {
        prepare(rule);
        buffer.append("rule ");
        if (!"".equals(rule.getLabel())) {
            buffer.append("[" + StringEscapeUtils.escapeXml(rule.getLabel())
                    + "]: ");
        }
        variableList.clear();
        this.visitNode(rule.getBody());
        if (rule.getRequires() != null) {
            buffer.append(" when ");
            this.visitNode(rule.getRequires());
        }
        if (rule.getEnsures() != null) {
            buffer.append(" ensures ");
            this.visitNode(rule.getEnsures());
        }
        this.visitNode(rule.getAttributes());
        buffer.append("\n");
        buffer.append("\n");
        return postpare();
    }

    @Override
    public Void visit(KApp kapp, Void _) {

        prepare(kapp);
        Term child = kapp.getChild();
        Term label = kapp.getLabel();
        if (label instanceof Token) {
            assert child instanceof KList : "child of KApp with Token is not KList";
            assert ((KList) child).isEmpty() : "child of KApp with Token is not empty";
            buffer.append(StringEscapeUtils.escapeXml(((Token) label).value()));
        } else {
            this.visitNode(label);
            buffer.append("(");
            this.visitNode(child);
            buffer.append(")");
        }
        return postpare();
    }

    @Override
    public Void visit(KSequence ksequence, Void _) {

        prepare(ksequence);
        java.util.List<Term> contents = ksequence.getContents();
        if (!contents.isEmpty()) {
            for (int i = 0; i < contents.size(); i++) {
                this.visitNode(contents.get(i));
                if (i != contents.size() - 1) {
                    buffer.append(StringEscapeUtils.escapeXml(" ~> "));
                }
            }
        } else {
            buffer.append(".K");
        }
        return postpare();
    }

    @Override
    public Void visit(TermCons termCons, Void _) {

        prepare(termCons);
        inTerm++;
        Production production = termCons.getProduction();
        if (production.isListDecl()) {
            UserList userList = (UserList) production.getItems().get(0);
            String separator = userList.getSeparator();
            java.util.List<Term> contents = termCons.getContents();
            this.visitNode(contents.get(0));
            buffer.append(StringEscapeUtils.escapeXml(separator) + " ");
            this.visitNode(contents.get(1));
        } else {
            int where = 0;
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    this.visitNode(termCons.getContents().get(where++));
                } else {
                    buffer.append(StringEscapeUtils
                            .escapeXml(((Terminal) productionItem)
                                    .getTerminal()));
                }
                if (i != production.getItems().size() - 1) {
                    buffer.append(" ");
                }
            }
        }
        inTerm--;
        return postpare();
    }

    @Override
    public Void visit(Rewrite rewrite, Void _) {

        prepare(rewrite);
        this.visitNode(rewrite.getLeft());
        buffer.append(StringEscapeUtils.escapeXml(" => "));
        this.visitNode(rewrite.getRight());
        return postpare();
    }

    @Override
    public Void visit(KLabelConstant kLabelConstant, Void _) {

        prepare(kLabelConstant);
        buffer.append(StringEscapeUtils.escapeXml(kLabelConstant.getLabel()
                .replaceAll("`", "``").replaceAll("\\(", "`(")
                .replaceAll("\\)", "`)")));
        return postpare();
    }

    @Override
    public Void visit(Collection collection, Void _) {

        prepare(collection);
        java.util.List<Term> contents = collection.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            this.visitNode(contents.get(i));
            if (i != contents.size() - 1) {
                if (inConfiguration && inTerm == 0) {
                    buffer.append("\n");
                } else {
                    buffer.append(" ");
                }
            }
        }
        if (contents.size() == 0) {
            buffer.append("."
                    + StringEscapeUtils.escapeXml(collection.getSort().getName()));
        }
        return postpare();
    }

    @Override
    public Void visit(CollectionItem collectionItem, Void _) {

        prepare(collectionItem);
        super.visit(collectionItem, _);
        return postpare();
    }

    @Override
    public Void visit(BagItem bagItem, Void _) {

        prepare(bagItem);
        buffer.append("BagItem(");
        super.visit(bagItem, _);
        buffer.append(")");
        return postpare();
    }

    @Override
    public Void visit(Hole hole, Void _) {

        buffer.append("HOLE");
        return postpare();
    }

    @Override
    public Void visit(FreezerHole hole, Void _) {

        prepare(hole);
        buffer.append("HOLE(" + hole.getIndex() + ")");
        return postpare();
    }

    @Override
    public Void visit(Freezer freezer, Void _) {

        prepare(freezer);
        this.visitNode(freezer.getTerm());
        return postpare();
    }

    @Override
    public Void visit(KInjectedLabel kInjectedLabel, Void _) {

        prepare(kInjectedLabel);
        Term term = kInjectedLabel.getTerm();
        if (term.getSort().isKSort()) {
            buffer.append(StringEscapeUtils.escapeXml(KInjectedLabel
                    .getInjectedSort(term.getSort()).getName()));
            buffer.append("2KLabel ");
        } else {
            buffer.append("# ");
        }
        this.visitNode(term);
        return postpare();
    }

    @Override
    public Void visit(KLabel kLabel, Void _) {

        prepare(kLabel);
        buffer.append("\n");
        buffer.append("Don't know how to pretty print KLabel");
        buffer.append("\n");
        super.visit(kLabel, _);
        return postpare();
    }

    @Override
    public Void visit(TermComment termComment, Void _) {

        prepare(termComment);
        buffer.append("<br/>");
        super.visit(termComment, _);
        return postpare();
    }

    @Override
    public Void visit(Bag bag, Void _) {

        prepare(bag);
        super.visit(bag, _);
        return postpare();
    }

    @Override
    public Void visit(org.kframework.kil.Ambiguity ambiguity, Void _) {

        prepare(ambiguity);
        buffer.append("amb(");
        buffer.append("\n");
        java.util.List<Term> contents = ambiguity.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            this.visitNode(contents.get(i));
            if (i != contents.size() - 1) {
                buffer.append(",");
                buffer.append("\n");
            }
        }
        buffer.append("\n");
        buffer.append(")");
        return postpare();
    }

    @Override
    public Void visit(org.kframework.kil.Context context, Void _) {

        prepare(context);
        buffer.append("context ");
        variableList.clear();
        this.visitNode(context.getBody());
        if (context.getRequires() != null) {
            buffer.append(" when ");
            this.visitNode(context.getRequires());
        }
        if (context.getEnsures() != null) {
            buffer.append(" ensures ");
            this.visitNode(context.getEnsures());
        }
        this.visitNode(context.getAttributes());
        buffer.append("\n");
        buffer.append("\n");
        return postpare();
    }

    @Override
    public Void visit(LiterateDefinitionComment literateDefinitionComment,
            Void _) {

        prepare(literateDefinitionComment);
        // buffer.append(literateDefinitionComment.getValue());
        // buffer.append("\n");
        return postpare();
    }

    @Override
    public Void visit(Require require, Void _) {

        prepare(require);
        if (!forEquivalence) {
            buffer.append("require \""
                    + StringEscapeUtils.escapeXml(require.getValue()) + "\"");
            buffer.append("\n");
        }
        return postpare();
    }

    @Override
    public Void visit(BackendTerm term, Void _) {

        prepare(term);
        buffer.append(StringEscapeUtils.escapeXml(term.getValue()));
        return postpare();
    }

    @Override
    public Void visit(Bracket br, Void _) {

        prepare(br);
        buffer.append("(");
        this.visitNode(br.getContent());
        buffer.append(")");
        return postpare();
    }

    @Override
    public Void visit(Cast c, Void _) {

        prepare(c);
        this.visitNode(c.getContent());
        buffer.append(" :");
        if (c.isSyntactic()) {
            buffer.append(":");
        }
        buffer.append(StringEscapeUtils.escapeXml(c.getSort().getName()));
        return postpare();
    }

    @Override
    public Void visit(Token t, Void _) {

        prepare(t);
        buffer.append(StringEscapeUtils.escapeXml("#token(\"" + t.tokenSort()
                + "\", \"" + t.value() + "\")"));
        return postpare();
    }

    private void prepare(ASTNode astNode) {

        if (!stack.empty()) {
            if (needsParanthesis(stack.peek(), astNode)) {
                buffer.append("(");
            }
        }
        stack.push(astNode);
    }

    private Void postpare() {

        ASTNode astNode = stack.pop();
        if (!stack.empty()) {
            if (needsParanthesis(stack.peek(), astNode)) {
                buffer.append(")");
            }
        }
        return null;
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
            if (context.isPriorityWrong(production.getKLabel(),
                    productionNext.getKLabel())) {
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
