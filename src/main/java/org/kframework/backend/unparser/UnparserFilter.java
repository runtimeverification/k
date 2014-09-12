// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.kframework.kil.*;
import org.kframework.kil.visitors.NonCachingVisitor;
import org.kframework.krun.ColorSetting;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.KRunOptions.OutputMode;
import org.kframework.utils.ColorUtil;
import org.kframework.utils.StringUtil;

import java.awt.Color;
import java.util.Iterator;
import java.util.Map.Entry;

public class UnparserFilter extends NonCachingVisitor {
    protected Indenter indenter = new Indenter();
    private boolean firstPriorityBlock = false;
    private boolean firstProduction = false;
    private boolean inConfiguration = false;
    private boolean addParentheses;
    private final KRunOptions.OutputMode outputMode;
    private int inTerm = 0;
    private ColorSetting color = ColorSetting.OFF;
    private Color terminalColor = Color.black;
    private boolean annotateLocation;
    public static int TAB = 4;
    private boolean forEquivalence = false; /* true when unparsing for kagreg; does not print configuration/imports/etc */
    private java.util.List<String> variableList = new java.util.LinkedList<String>();
    private java.util.Map<Production, Integer> priorities = null;
    private java.util.Stack<ASTNode> stack = new java.util.Stack<ASTNode>();

    public void setForEquivalence() {
        forEquivalence = true;
    }

    public void setIndenter(Indenter indenter) {
        this.indenter = indenter;
    }

    public UnparserFilter(org.kframework.kil.loader.Context context) {
        this(false, context);
    }

    public UnparserFilter(boolean inConfiguration, org.kframework.kil.loader.Context context) {
        this(inConfiguration, false, context);
    }

    public UnparserFilter(boolean inConfiguration, boolean color, org.kframework.kil.loader.Context context) {
        this(inConfiguration, color ? ColorSetting.ON : ColorSetting.OFF, OutputMode.PRETTY, context);
    }

    public UnparserFilter(boolean inConfiguration, ColorSetting color, OutputMode outputMode, org.kframework.kil.loader.Context context) {
        this(inConfiguration, color, outputMode, false, context);
    }

    public UnparserFilter(boolean inConfiguration, ColorSetting color, OutputMode outputMode, boolean annotateLocation, org.kframework.kil.loader.Context context) {
        super(context);
        this.inConfiguration = inConfiguration;
        this.color = color;
        this.inTerm = 0;
        this.addParentheses = outputMode != OutputMode.SMART;
        this.annotateLocation = annotateLocation;
        this.outputMode = outputMode;
        //TODO(dwightguth): clean up pretty printing so we don't need this ugly hack
        if (context.colorOptions != null) {
            terminalColor = context.colorOptions.terminalColor();
        }
    }

    public String getResult() {
        return indenter.toString();
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
            indenter.write("imports " + imp.getName());
            indenter.endLine();
        }
        return postpare();
    }

    @Override
    public Void visit(Module mod, Void _) {
        prepare(mod);
        if (!mod.isPredefined()) {
            if (!forEquivalence) {
                indenter.write("module " + mod.getName());
                indenter.endLine();
                indenter.endLine();
                indenter.indent(TAB);
            }
            super.visit(mod, _);
            if (!forEquivalence) {
                indenter.unindent();
                indenter.write("endmodule");
                indenter.endLine();
                indenter.endLine();
            }
        }
        return postpare();
    }

    @Override
    public Void visit(Syntax syn, Void _) {
        prepare(syn);
        firstPriorityBlock = true;
        indenter.write("syntax " + syn.getDeclaredSort().getName());
        indenter.indentToCurrent();
        if (syn.getPriorityBlocks() != null)
            for (PriorityBlock pb : syn.getPriorityBlocks()) {
                this.visitNode(pb);
            }
        indenter.unindent();
        indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(PriorityBlock priorityBlock, Void _) {
        prepare(priorityBlock);
        if (firstPriorityBlock) {
            indenter.write(" ::=");
        } else {
            indenter.write("  >");
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
            indenter.write(" ");
        } else {
            indenter.write("  | ");
        }
        firstProduction = false;
        for (int i = 0; i < prod.getItems().size(); ++i) {
            ProductionItem pi = prod.getItems().get(i);
            this.visitNode(pi);
            if (i != prod.getItems().size() - 1) {
                indenter.write(" ");
            }
        }
        if (!prod.getAttributes().isEmpty()) {
            indenter.write(" ");
            indenter.write("[");
            this.visitNode(prod.getAttributes());
            indenter.write("]");
        }
        indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(NonTerminal sort, Void _) {
        prepare(sort);
        indenter.write(sort.getName());
        super.visit(sort, _);
        return postpare();
    }

    @Override
    public Void visit(Terminal terminal, Void _) {
        prepare(terminal);
        indenter.write("\"" + terminal.getTerminal() + "\"");
        super.visit(terminal, _);
        return postpare();
    }

    @Override
    public Void visit(UserList userList, Void _) {
        prepare(userList);
        indenter.write("List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}");
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
                indenter.write(",, ");
            }
        }
        if (termList.size() == 0) {
            indenter.write(".KList");
        }
        return postpare();
    }

    @Override
    public Void visit(Attributes attributes, Void _) {
        prepare(attributes);
        if (!attributes.isEmpty()) {
            Iterator<Attribute<?>> iter = attributes.values().iterator();
            for (int i = 0; i < attributes.size(); ++i) {
                this.visitNode(iter.next());
                if (i != attributes.size() - 1) {
                    indenter.write(", ");
                }
            }
        }
        return postpare();
    }

    @Override
    public Void visit(Attribute attribute, Void _) {
        prepare(attribute);
        indenter.write(attribute.toString());
        return postpare();
    }

    @Override
    public Void visit(Configuration configuration, Void _) {
        prepare(configuration);
        if (!forEquivalence) {
            indenter.write("configuration");
            indenter.endLine();
            indenter.indent(TAB);
            inConfiguration = true;
            this.visitNode(configuration.getBody());
            inConfiguration = false;
            indenter.unindent();
            indenter.endLine();
            indenter.endLine();
        }
        return postpare();
    }

    @Override
    public Void visit(Cell cell, Void _) {
        prepare(cell);
        String attributes = "";
        for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
            if (entry.getKey() != "ellipses") {
                attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";
            }
        }
        String colorCode = "";
        Cell declaredCell = context.cells.get(cell.getLabel());
        if (declaredCell != null) {
            String declaredColor = declaredCell.getCellAttributes().get("color");
            if (declaredColor != null) {
                colorCode = ColorUtil.RgbToAnsi(ColorUtil.colors().get(declaredColor), color, terminalColor);
                indenter.write(colorCode);
            }
        }

        indenter.write("<" + cell.getLabel() + attributes + ">");
        if (inConfiguration && inTerm == 0) {
            indenter.endLine();
            indenter.indent(TAB);
        } else {
            if (cell.hasLeftEllipsis()) {
                indenter.write("... ");
            } else {
                indenter.write(" ");
            }
        }
        if (!colorCode.equals("")) {
            indenter.write(ColorUtil.ANSI_NORMAL);
        }
        this.visitNode(cell.getContents());
        indenter.write(colorCode);
        if (inConfiguration && inTerm == 0) {
            indenter.endLine();
            indenter.unindent();
        } else {
            if (cell.hasRightEllipsis()) {
                indenter.write(" ...");
            } else {
                indenter.write(" ");
            }
        }
        indenter.write("</" + cell.getLabel() + ">");
        if (!colorCode.equals("")) {
            indenter.write(ColorUtil.ANSI_NORMAL);
        }
        return postpare();
    }

    @Override
    public Void visit(Variable variable, Void _) {
        prepare(variable);
        if (variable.isFreshVariable())
            indenter.write("?");
        else if (variable.isFreshConstant())
            indenter.write("!");
        indenter.write(variable.getName());
        if (!variableList.contains(variable.getName())) {
            indenter.write(":" + variable.getSort());
            variableList.add(variable.getName());

            if (variable.getAttributes().size() > 0) {
                indenter.write("{");
                this.visitNode(variable.getAttributes());
                indenter.write("}");
            }
        }
        return postpare();
    }

    @Override
    public Void visit(ListTerminator terminator, Void _) {
        prepare(terminator);
        indenter.write(terminator.toString());
        return postpare();
    }

    @Override
    public Void visit(Rule rule, Void _) {
        prepare(rule);
        indenter.write("rule ");
        if (!"".equals(rule.getLabel())) {
            indenter.write("[" + rule.getLabel() + "]: ");
        }
        variableList.clear();
        this.visitNode(rule.getBody());
        if (rule.getRequires() != null) {
            indenter.write(" when ");
            this.visitNode(rule.getRequires());
        }
        if (rule.getEnsures() != null) {
            indenter.write(" ensures ");
            this.visitNode(rule.getEnsures());
        }
        if (!rule.getAttributes().isEmpty()) {
            indenter.write(" ");
            indenter.write("[");
            this.visitNode(rule.getAttributes());
            indenter.write("]");
        }
        indenter.endLine();
        indenter.endLine();
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
            indenter.write(((Token) label).value());
        } else if ((outputMode == OutputMode.PRETTY || outputMode == OutputMode.NO_WRAP)
                && (label instanceof KLabelConstant) && ((KLabelConstant) label).getLabel().contains("'_")) {

            String rawLabel = "("+((KLabelConstant) label).getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)").replaceAll("'", "") + ")";

            if (child instanceof KList) {
                java.util.List<Term> termList = ((KList)child).getContents();

                if(termList.size()==0){
                    indenter.write(rawLabel);
                } else{
                    int i = 0;
                    String [] rawLabelList = rawLabel.split("_");
                    for (i = 0; i < termList.size(); ++i) {
                        indenter.write(rawLabelList[i]);
                        if (i > 0) {
                            indenter.write(" ");
                        }
                        this.visitNode(termList.get(i));
                        if (i < termList.size() - 1) {
                            indenter.write(" ");
                        }
                    }
                    indenter.write(rawLabelList[i]);
                }
            }
            else {
                // child is a KList variable
                indenter.write("(");
                this.visitNode(child);
                indenter.write(")");
            }
        }
        else {
            this.visitNode(label);
            indenter.write("(");
            this.visitNode(child);
            indenter.write(")");
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
                    indenter.write(" ~> ");
                }
            }
        } else {
            indenter.write(".K");
        }
        return postpare();
    }

    @Override
    public Void visit(Constant t, Void _) {
        prepare(t);
        indenter.write(t.getValue());
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
            if (contents.size() == 0) {
                indenter.write("." + production.getSort());
            } else {
                this.visitNode(contents.get(0));
                if (!(contents.get(1) instanceof ListTerminator)) {
                    indenter.write(separator + " ");
                    this.visitNode(contents.get(1));
                }
            }
        } else {
            int where = 0;
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    this.visitNode(termCons.getContents().get(where++));
                } else {
                    indenter.write(((Terminal) productionItem).getTerminal());
                }
                // TODO(YilongL): not sure I can simply remove the following code
                if (i != production.getItems().size() - 1) {
                    indenter.write(" ");
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
        indenter.write(" => ");
        this.visitNode(rewrite.getRight());
        return postpare();
    }

    @Override
    public Void visit(KLabelConstant kLabelConstant, Void _) {
        prepare(kLabelConstant);
        indenter.write(kLabelConstant.getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)"));
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
                    indenter.endLine();
                } else {
                    indenter.write(" ");
                }
            }
        }
        if (contents.size() == 0) {
            indenter.write("." + collection.getSort());
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
        indenter.write("BagItem(");
        super.visit(bagItem, _);
        indenter.write(")");
        return postpare();
    }

    @Override
    public Void visit(Hole hole, Void _) {
        prepare(hole);
        indenter.write("HOLE");
        return postpare();
    }

    @Override
    public Void visit(FreezerHole hole, Void _) {
        prepare(hole);
        indenter.write("HOLE(" + hole.getIndex() + ")");
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
            indenter.write(KInjectedLabel.getInjectedSort(term.getSort()).getName());
            indenter.write("2KLabel ");
        } else {
            indenter.write("# ");
        }
        this.visitNode(term);
        return postpare();
    }

    @Override
    public Void visit(KLabel kLabel, Void _) {
        prepare(kLabel);
//        indenter.endLine();
//        indenter.write("Don't know how to pretty print KLabel");
//        indenter.endLine();
        super.visit(kLabel, _);
        return postpare();
    }

    @Override
    public Void visit(TermComment termComment, Void _) {
        prepare(termComment);
        indenter.write("<br/>");
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
        indenter.write("amb(");
        indenter.endLine();
        indenter.indent(TAB);
        java.util.List<Term> contents = ambiguity.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            this.visitNode(contents.get(i));
            if (i != contents.size() - 1) {
                indenter.write(",");
                indenter.endLine();
            }
        }
        indenter.endLine();
        indenter.unindent();
        indenter.write(")");
        return postpare();
    }

    @Override
    public Void visit(org.kframework.kil.Context context, Void _) {
        prepare(context);
        indenter.write("context ");
        variableList.clear();
        this.visitNode(context.getBody());
        if (context.getRequires() != null) {
            indenter.write(" when ");
            this.visitNode(context.getRequires());
        }
        if (context.getEnsures() != null) {
            indenter.write(" ensures ");
            this.visitNode(context.getEnsures());
        }
        if (!context.getAttributes().isEmpty()) {
            indenter.write(" ");
            indenter.write("[");
            this.visitNode(context.getAttributes());
            indenter.write("]");
        }
        indenter.endLine();
        indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(LiterateDefinitionComment literateDefinitionComment, Void _) {
        prepare(literateDefinitionComment);
        // indenter.write(literateDefinitionComment.getValue());
        // indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(Require require, Void _) {
        prepare(require);
        if (!forEquivalence) {
            indenter.write("require \"" + require.getValue() + "\"");
            indenter.endLine();
        }
        return postpare();
    }

    @Override
    public Void visit(BackendTerm term, Void _) {
        prepare(term);
        indenter.write(term.getValue());
        return postpare();
    }

    @Override
    public Void visit(Bracket br, Void _) {
        prepare(br);
        indenter.write("(");
        this.visitNode(br.getContent());
        indenter.write(")");
        return postpare();
    }

    @Override
    public Void visit(Cast c, Void _) {
        prepare(c);
        this.visitNode(c.getContent());
        indenter.write(" :");
        if (c.isSyntactic()) {
            indenter.write(":");
        }
        indenter.write(c.getSort().getName());
        if (c.getAttributes().size() > 0) {
            indenter.write("{");
            this.visitNode(c.getAttributes());
            indenter.write("}");
        }
        return postpare();
    }

    @Override
    public Void visit(Token t, Void _) {
        prepare(t);
        indenter.write("#token(\"" + t.tokenSort() + "\", \"" + t.value() + "\")");
        return postpare();
    }

    protected void prepare(ASTNode astNode) {
        if (!stack.empty()) {
            if (needsParenthesis(stack.peek(), astNode)) {
                indenter.write("(");
            }
        }
        stack.push(astNode);
        if (annotateLocation) {
            if (astNode.getLocation() == null) {
                astNode.setLocation(new Location(indenter.getLineNo(), indenter.getColNo(), 0, 0));
            } else {
                astNode.getLocation().lineStart = indenter.getLineNo();
                astNode.getLocation().columnStart = indenter.getColNo();
            }
        }
    }

    protected Void postpare() {
        ASTNode astNode = stack.pop();
        if (!stack.empty()) {
            if (needsParenthesis(stack.peek(), astNode)) {
                indenter.write(")");
            }
        }
        if (annotateLocation) {
            astNode.getLocation().lineEnd = indenter.getLineNo();
            astNode.getLocation().columnEnd = indenter.getColNo();
        }
        return null;
    }

    private boolean needsParenthesis(ASTNode upper, ASTNode astNode) {
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

    public java.util.Map<Production, Integer> getPriorities() {
        return priorities;
    }

    public void setPriorities(java.util.Map<Production, Integer> priorities) {
        this.priorities = priorities;
    }

    public void setInConfiguration(boolean inConfiguration) {
        this.inConfiguration = inConfiguration;
    }
}
