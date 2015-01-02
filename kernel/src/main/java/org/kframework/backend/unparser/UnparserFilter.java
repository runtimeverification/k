// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.kframework.kil.*;
import org.kframework.kil.visitors.NonCachingVisitor;
import org.kframework.krun.ColorSetting;
import org.kframework.utils.ColorUtil;

import java.awt.Color;
import java.util.Iterator;
import java.util.Map.Entry;

public class UnparserFilter extends NonCachingVisitor {
    protected Indenter indenter = new Indenter();
    private boolean firstPriorityBlock = false;
    private boolean firstProduction = false;
    private boolean inConfiguration = false;
    private int inTerm = 0;
    private ColorSetting color = ColorSetting.OFF;
    private Color terminalColor = Color.black;
    private boolean annotateLocation;
    public static int TAB = 4;
    private java.util.List<String> variableList = new java.util.LinkedList<String>();
    private java.util.Stack<ASTNode> stack = new java.util.Stack<ASTNode>();

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
        this(inConfiguration, color ? ColorSetting.ON : ColorSetting.OFF, OutputModes.PRETTY, context);
    }

    public UnparserFilter(boolean inConfiguration, ColorSetting color, OutputModes outputMode, org.kframework.kil.loader.Context context) {
        this(inConfiguration, color, outputMode, false, context);
    }

    public UnparserFilter(boolean inConfiguration, ColorSetting color, OutputModes outputMode, boolean annotateLocation, org.kframework.kil.loader.Context context) {
        super(context);
        this.inConfiguration = inConfiguration;
        this.color = color;
        this.inTerm = 0;
        this.annotateLocation = annotateLocation;
        if (outputMode == OutputModes.NO_WRAP) {
            indenter.setWidth(-1);
        }
        if (context.colorOptions != null) {
            terminalColor = context.colorOptions.terminalColor();
        }
    }

    public String getResult() {
        return indenter.toString();
    }

    @Override
    public Void visit(Definition def, Void _void) {
        prepare(def);
        super.visit(def, _void);
        return postpare();
    }

    @Override
    public Void visit(Import imp, Void _void) {
        prepare(imp);
        indenter.write("imports " + imp.getName());
        indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(Module mod, Void _void) {
        prepare(mod);
        if (!mod.isPredefined()) {
            indenter.write("module " + mod.getName());
            indenter.endLine();
            indenter.endLine();
            indenter.indent(TAB);
            super.visit(mod, _void);
            indenter.unindent();
            indenter.write("endmodule");
            indenter.endLine();
            indenter.endLine();
        }
        return postpare();
    }

    @Override
    public Void visit(Syntax syn, Void _void) {
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
    public Void visit(PriorityBlock priorityBlock, Void _void) {
        prepare(priorityBlock);
        if (firstPriorityBlock) {
            indenter.write(" ::=");
        } else {
            indenter.write("  >");
        }
        firstPriorityBlock = false;
        firstProduction = true;
        super.visit(priorityBlock, _void);
        return postpare();
    }

    @Override
    public Void visit(Production prod, Void _void) {
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
    public Void visit(NonTerminal sort, Void _void) {
        prepare(sort);
        indenter.write(sort.getName());
        super.visit(sort, _void);
        return postpare();
    }

    @Override
    public Void visit(Terminal terminal, Void _void) {
        prepare(terminal);
        indenter.write("\"" + terminal.getTerminal() + "\"");
        super.visit(terminal, _void);
        return postpare();
    }

    @Override
    public Void visit(UserList userList, Void _void) {
        prepare(userList);
        indenter.write("List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}");
        super.visit(userList, _void);
        return postpare();
    }

    @Override
    public Void visit(KList listOfK, Void _void) {
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
    public Void visit(Attributes attributes, Void _void) {
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
    public Void visit(Attribute attribute, Void _void) {
        prepare(attribute);
        indenter.write(attribute.toString());
        return postpare();
    }

    @Override
    public Void visit(Configuration configuration, Void _void) {
        prepare(configuration);
        indenter.write("configuration");
        indenter.endLine();
        indenter.indent(TAB);
        inConfiguration = true;
        this.visitNode(configuration.getBody());
        inConfiguration = false;
        indenter.unindent();
        indenter.endLine();
        indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(Cell cell, Void _void) {
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

        /* if the contents of this cell is a bag, sort them properly */
        Term contents = cell.getContents();
        this.visitNode(contents);

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
    public Void visit(Variable variable, Void _void) {
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
    public Void visit(ListTerminator terminator, Void _void) {
        prepare(terminator);
        indenter.write(terminator.toString());
        return postpare();
    }

    @Override
    public Void visit(Rule rule, Void _void) {
        prepare(rule);
        indenter.write("rule ");
        if (!"".equals(rule.getLabel())) {
            indenter.write("[" + rule.getLabel() + "]: ");
        }
        variableList.clear();
        this.visitNode(rule.getBody());
        if (rule.getRequires() != null) {
            indenter.write(" requires ");
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
    public Void visit(KApp kapp, Void _void) {
        prepare(kapp);
        this.visitNode(kapp.getLabel());
        indenter.write("(");
        this.visitNode(kapp.getChild());
        indenter.write(")");
        return postpare();
    }

    @Override
    public Void visit(KSequence ksequence, Void _void) {
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

    /*
     * TermCons actually controls most input terms, ie. most input terms will
     * have classes TermCons.
     * The way to deal with TermCons is that if the syntax of the given definition allowed,
     * we will put parentheses surrounding a TermCons term.
     * We will also delete the final ListTerminator if the input mode is pretty printing.
     */
    @Override
    public Void visit(TermCons termCons, Void _void) {
        prepare(termCons);
        inTerm++;
        Production production = termCons.getProduction();
        if (production.isListDecl()) {
            UserList userList = (UserList) production.getItems().get(0);
            String separator = userList.getSeparator();
            java.util.List<Term> contents = termCons.getContents();
            this.visitNode(contents.get(0));
            indenter.write(separator + " ");
            this.visitNode(contents.get(1));
        } else {
            int where = 0;
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    Term subterm = termCons.getContents().get(where);
                    if (!isDataStructure(termCons) && isDataStructure(subterm)) {
                        indenter.endLine();
                        indenter.indent(TAB);
                        this.visitNode(subterm);
                        indenter.unindent();
                    } else {
                        this.visitNode(subterm);
                    }
                    where++;
                } else {
                    indenter.write(((Terminal) productionItem).getTerminal());
                }
                // TODO(YilongL): not sure I can simply remove the following code
                if (i != production.getItems().size() - 1) {
                    if (isDataStructure(termCons)) {
                        indenter.endLine();
                    } else {
                        indenter.write(" ");
                    }
                }
            }
        }
        inTerm--;
        return postpare();
    }

    @Override
    public Void visit(Constant constant, Void _void) {
        prepare(constant);
        indenter.write(constant.getValue());
        return postpare();
    }

    private boolean isDataStructure(Term t) {
        if (t instanceof TermCons) {
            Production production = ((TermCons) t).getProduction();

            DataStructureSort dsSort = context.dataStructureSortOf(production.getSort());
            if (dsSort != null && dsSort.constructorLabel().equals(production.getKLabel())) {
                //is a constructor of a data structure
                //special case a new line between each item and indentation
                return true;
            }
            return false;
        } else if (t instanceof Bracket) {
            return isDataStructure(((Bracket) t).getContent());
        } else {
            return false;
        }
    }

    @Override
    public Void visit(Rewrite rewrite, Void _void) {
        prepare(rewrite);
        this.visitNode(rewrite.getLeft());
        indenter.write(" => ");
        this.visitNode(rewrite.getRight());
        return postpare();
    }

    @Override
    public Void visit(KLabelConstant kLabelConstant, Void _void) {
        prepare(kLabelConstant);
        indenter.write(kLabelConstant.getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)").replaceAll(",", "`,"));
        return postpare();
    }

    @Override
    public Void visit(Collection collection, Void _void) {
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
    public Void visit(CollectionItem collectionItem, Void _void) {
        prepare(collectionItem);
        super.visit(collectionItem, _void);
        return postpare();
    }

    @Override
    public Void visit(BagItem bagItem, Void _void) {
        prepare(bagItem);
        indenter.write("BagItem(");
        super.visit(bagItem, _void);
        indenter.write(")");
        return postpare();
    }

    @Override
    public Void visit(Hole hole, Void _void) {
        prepare(hole);
        indenter.write("HOLE");
        return postpare();
    }

    @Override
    public Void visit(FreezerHole hole, Void _void) {
        prepare(hole);
        indenter.write("HOLE(" + hole.getIndex() + ")");
        return postpare();
    }

    @Override
    public Void visit(Freezer freezer, Void _void) {
        prepare(freezer);
        this.visitNode(freezer.getTerm());
        return postpare();
    }

    @Override
    public Void visit(KInjectedLabel kInjectedLabel, Void _void) {
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
    public Void visit(TermComment termComment, Void _void) {
        prepare(termComment);
        indenter.write("<br/>");
        super.visit(termComment, _void);
        return postpare();
    }

    @Override
    public Void visit(Bag bag, Void _void) {
        prepare(bag);
        super.visit(bag, _void);
        return postpare();
    }

    @Override
    public Void visit(org.kframework.kil.Ambiguity ambiguity, Void _void) {
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
    public Void visit(org.kframework.kil.Context context, Void _void) {
        prepare(context);
        indenter.write("context ");
        variableList.clear();
        this.visitNode(context.getBody());
        if (context.getRequires() != null) {
            indenter.write(" requires ");
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
    public Void visit(LiterateDefinitionComment literateDefinitionComment, Void _void) {
        prepare(literateDefinitionComment);
        // indenter.write(literateDefinitionComment.getValue());
        // indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(Require require, Void _void) {
        prepare(require);
        indenter.write("require \"" + require.getValue() + "\"");
        indenter.endLine();
        return postpare();
    }

    @Override
    public Void visit(BackendTerm term, Void _void) {
        prepare(term);
        indenter.write(term.getValue());
        return postpare();
    }

    @Override
    public Void visit(Bracket br, Void _void) {
        prepare(br);
        indenter.write("(");
        this.visitNode(br.getContent());
        indenter.write(")");
        return postpare();
    }

    @Override
    public Void visit(Cast c, Void _void) {
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
    public Void visit(Token t, Void _void) {
        prepare(t);
        indenter.write("#token(\"" + t.tokenSort() + "\", \"" + t.value() + "\")");
        return postpare();
    }

    protected void prepare(ASTNode astNode) {
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
        if (annotateLocation) {
            astNode.getLocation().lineEnd = indenter.getLineNo();
            astNode.getLocation().columnEnd = indenter.getColNo();
        }
        return null;
    }

    public void setInConfiguration(boolean inConfiguration) {
        this.inConfiguration = inConfiguration;
    }
}
