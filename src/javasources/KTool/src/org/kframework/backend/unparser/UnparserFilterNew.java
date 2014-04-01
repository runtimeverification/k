package org.kframework.backend.unparser;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.krun.ColorSetting;
import org.kframework.krun.K;
import org.kframework.utils.ColorUtil;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

public class UnparserFilterNew extends BasicVisitor {
    protected Indenter indenter = new Indenter();
    private boolean firstPriorityBlock = false;
    private boolean firstProduction = false;
    private boolean inConfiguration = false;
    private boolean addParentheses;
    private int inTerm = 0;
    private ColorSetting color = ColorSetting.OFF;
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
    
    public UnparserFilterNew(org.kframework.kil.loader.Context context) {
        this(false, context);
    }

    public UnparserFilterNew(boolean inConfiguration, org.kframework.kil.loader.Context context) {
        this(inConfiguration, false, context);
    }

    public UnparserFilterNew(boolean inConfiguration, boolean color, org.kframework.kil.loader.Context context) {
        this(inConfiguration, color ? ColorSetting.ON : ColorSetting.OFF, true, context);
    }

    public UnparserFilterNew(boolean inConfiguration, ColorSetting color, boolean addParentheses, org.kframework.kil.loader.Context context) {
        this(inConfiguration, color, addParentheses, false, context);
    }

    public UnparserFilterNew(boolean inConfiguration, ColorSetting color, boolean addParentheses, boolean annotateLocation, org.kframework.kil.loader.Context context) {
        super(context);
        this.inConfiguration = inConfiguration;
        this.color = color;
        this.inTerm = 0;
        this.addParentheses = addParentheses;
        this.annotateLocation = annotateLocation;
    }

    public String getResult() {
        return indenter.toString();
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
            indenter.write("imports " + imp.getName());
            indenter.endLine();
        }
        postpare();
    }

    @Override
    public void visit(Module mod) {
        prepare(mod);
        if (!mod.isPredefined()) {
            if (!forEquivalence) {
                indenter.write("module " + mod.getName());
                indenter.endLine();
                indenter.endLine();
                indenter.indent(TAB);
            }
            super.visit(mod);
            if (!forEquivalence) {
                indenter.unindent();
                indenter.write("endmodule");
                indenter.endLine();
                indenter.endLine();
            }
        }
        postpare();
    }

    @Override
    public void visit(Syntax syn) {
        prepare(syn);
        firstPriorityBlock = true;
        indenter.write("syntax " + syn.getSort().getName());
        indenter.indentToCurrent();
        if (syn.getPriorityBlocks() != null)
            for (PriorityBlock pb : syn.getPriorityBlocks()) {
                pb.accept(this);
            }
        indenter.unindent();
        indenter.endLine();
        postpare();
    }

    @Override
    public void visit(PriorityBlock priorityBlock) {
        prepare(priorityBlock);
        if (firstPriorityBlock) {
            indenter.write(" ::=");
        } else {
            indenter.write("  >");
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
            indenter.write(" ");
        } else {
            indenter.write("  | ");
        }
        firstProduction = false;
        for (int i = 0; i < prod.getItems().size(); ++i) {
            ProductionItem pi = prod.getItems().get(i);
            pi.accept(this);
            if (i != prod.getItems().size() - 1) {
                indenter.write(" ");
            }
        }
        prod.getAttributes().accept(this);
        indenter.endLine();
        postpare();
    }

    @Override
    public void visit(Sort sort) {
        prepare(sort);
        indenter.write(sort.getName());
        super.visit(sort);
        postpare();
    }

    @Override
    public void visit(Terminal terminal) {
        prepare(terminal);
        indenter.write("\"" + terminal.getTerminal() + "\"");
        super.visit(terminal);
        postpare();
    }

    @Override
    public void visit(UserList userList) {
        prepare(userList);
        indenter.write("List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}");
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
                indenter.write(",, ");
            }
        }
        if (termList.size() == 0) {
            indenter.write(".KList");
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
            indenter.write(" ");
            indenter.write("[");
            for (int i = 0; i < attributeList.size(); ++i) {
                attributeList.get(i).accept(this);
                if (i != attributeList.size() - 1) {
                    indenter.write(", ");
                }
            }
            indenter.write("]");
        }
        postpare();
    }

    @Override
    public void visit(Attribute attribute) {
        prepare(attribute);
        indenter.write(attribute.getKey());
        if (!attribute.getValue().equals("")) {
            indenter.write("(" + attribute.getValue() + ")");
        }
        postpare();
    }

    @Override
    public void visit(Configuration configuration) {
        prepare(configuration);
        if (!forEquivalence) {
            indenter.write("configuration");
            indenter.endLine();
            indenter.indent(TAB);
            inConfiguration = true;
            configuration.getBody().accept(this);
            inConfiguration = false;
            indenter.unindent();
            indenter.endLine();
            indenter.endLine();
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
        if (declaredCell != null) {
            String declaredColor = declaredCell.getCellAttributes().get("color");
            if (declaredColor != null) {
                colorCode = ColorUtil.RgbToAnsi(ColorUtil.colors.get(declaredColor), color);
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
        cell.getContents().accept(this);
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
        postpare();
    }

    @Override
    public void visit(Variable variable) {
        prepare(variable);
        if (variable.isFresh())
            indenter.write("?");
        indenter.write(variable.getName());
        if (!variableList.contains(variable.getName())) {
            indenter.write(":" + variable.getSort());
            variableList.add(variable.getName());
        }
        postpare();
    }

    @Override
    public void visit(ListTerminator terminator) {
        prepare(terminator);
        indenter.write(terminator.toString());
        postpare();
    }

    @Override
    public void visit(Rule rule) {
        prepare(rule);
        indenter.write("rule ");
        if (!"".equals(rule.getLabel())) {
            indenter.write("[" + rule.getLabel() + "]: ");
        }
        variableList.clear();
        rule.getBody().accept(this);
        if (rule.getRequires() != null) {
            indenter.write(" when ");
            rule.getRequires().accept(this);
        }
        if (rule.getEnsures() != null) {
            indenter.write(" ensures ");
            rule.getEnsures().accept(this);
        }
        rule.getAttributes().accept(this);
        indenter.endLine();
        indenter.endLine();
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
            
            List<Terminal> temp = this.findRightSyntax(label.getSort());
            if(!temp.isEmpty()){
                indenter.write(temp.get(0).getTerminal());
            }
            
            indenter.write(((Token) label).value());
            
            if(temp.size()>1){
                
                indenter.write(temp.get(1).getTerminal());
            }
        } else if (K.output_mode.equals(K.PRETTY) && (label instanceof KLabelConstant) && ((KLabelConstant) label).getLabel().contains("'_")) {
            
            String rawLabel = null;
            List<Terminal> temp = this.findRightSyntax(label.getSort());
            if(!temp.isEmpty()){
                if(temp.size()>1){
                    rawLabel = temp.get(0).getTerminal()
                            +((KLabelConstant) label).getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)").replaceAll("'", "") + 
                            temp.get(1).getTerminal();

                } else {
                    rawLabel = temp.get(0).getTerminal()
                            +((KLabelConstant) label).getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)").replaceAll("'", "")+" ";
                }
            } else {
                rawLabel = " "+((KLabelConstant) label).getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)").replaceAll("'", "")+" ";
            }
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
                        termList.get(i).accept(this);
                    }
                    indenter.write(rawLabelList[i]);
                }
            }
            else {
                // child is a KList variable
                indenter.write("(");
                child.accept(this);
                indenter.write(")");
            }
        }
        else {
            label.accept(this);
            indenter.write("(");
            child.accept(this);
            indenter.write(")");
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
                    indenter.write(" ~> ");
                }
            }
        } else {
            indenter.write(".K");
        }
        postpare();
    }

    /*
     * TermCons actually controls most input terms, ie. most input terms will
     * have classes TermCons.
     * The way to deal with TermCons is that if the syntax of the given definition allowed,
     * we will put parentheses surrounding a TermCons term.
     * We will also delete the final ListTerminator if the input mode is pretty printing. 
     */
    @Override
    public void visit(TermCons termCons) {
        //prepare(termCons);
        List<Terminal> temp = this.findRightSyntax(termCons.getSort());
        if(!temp.isEmpty()){
            indenter.write(temp.get(0).getTerminal());
        }
        inTerm++;
        Production production = termCons.getProduction();
        if (production.isListDecl()) {
            UserList userList = (UserList) production.getItems().get(0);
            String separator = userList.getSeparator();
            java.util.List<Term> contents = termCons.getContents();
            contents.get(0).accept(this);
            if (!(contents.get(1) instanceof ListTerminator) 
                    || (! (K.output_mode.equals(K.PRETTY)) && ! (K.output_mode.equals(K.KORE)))) {
                indenter.write(separator + " ");
                contents.get(1).accept(this);
            }
        } else {
            int where = 0;
            for (int i = 0; i < production.getItems().size(); ++i) {
                ProductionItem productionItem = production.getItems().get(i);
                if (!(productionItem instanceof Terminal)) {
                    if(!(termCons.getContents().get(where) instanceof ListTerminator) || (! (K.output_mode.equals(K.PRETTY)) && ! (K.output_mode.equals(K.KORE)))){
                            termCons.getContents().get(where++).accept(this);
                    } else {
                        where++;
                    }
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
        if(temp.size()>1){
            
            indenter.write(temp.get(1).getTerminal());
        }
        //postpare();
    }

    @Override
    public void visit(Rewrite rewrite) {
        prepare(rewrite);
        rewrite.getLeft().accept(this);
        indenter.write(" => ");
        rewrite.getRight().accept(this);
        postpare();
    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        prepare(kLabelConstant);
        indenter.write(kLabelConstant.getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)"));
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
                    indenter.endLine();
                } else {
                    indenter.write(" ");
                }
            }
        }
        if (contents.size() == 0) {
            indenter.write("." + collection.getSort());
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
        indenter.write("BagItem(");
        super.visit(bagItem);
        indenter.write(")");
        postpare();
    }

    @Override
    public void visit(ListItem listItem) {
        prepare(listItem);
        indenter.write("ListItem(");
        super.visit(listItem);
        indenter.write(")");
        postpare();
    }

    @Override
    public void visit(SetItem setItem) {
        prepare(setItem);
        indenter.write("SetItem(");
        super.visit(setItem);
        indenter.write(")");
        postpare();
    }

    @Override
    public void visit(MapItem mapItem) {
        prepare(mapItem);
        mapItem.getKey().accept(this);
        indenter.write(" |-> ");
        mapItem.getValue().accept(this);
        postpare();
    }

    @Override
    public void visit(Hole hole) {
        prepare(hole);
        indenter.write("HOLE");
        postpare();
    }

    @Override
    public void visit(FreezerHole hole) {
        prepare(hole);
        indenter.write("HOLE(" + hole.getIndex() + ")");
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
            indenter.write(KInjectedLabel.getInjectedSort(term.getSort()));
            indenter.write("2KLabel ");
        } else {
            indenter.write("# ");
        }
        term.accept(this);
        postpare();
    }

    @Override
    public void visit(KLabel kLabel) {
        prepare(kLabel);
        indenter.endLine();
        indenter.write("Don't know how to pretty print KLabel");
        indenter.endLine();
        super.visit(kLabel);
        postpare();
    }

    @Override
    public void visit(TermComment termComment) {
        prepare(termComment);
        indenter.write("<br/>");
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
        indenter.write("amb(");
        indenter.endLine();
        indenter.indent(TAB);
        java.util.List<Term> contents = ambiguity.getContents();
        for (int i = 0; i < contents.size(); ++i) {
            contents.get(i).accept(this);
            if (i != contents.size() - 1) {
                indenter.write(",");
                indenter.endLine();
            }
        }
        indenter.endLine();
        indenter.unindent();
        indenter.write(")");
        postpare();
    }

    @Override
    public void visit(org.kframework.kil.Context context) {
        prepare(context);
        indenter.write("context ");
        variableList.clear();
        context.getBody().accept(this);
        if (context.getRequires() != null) {
            indenter.write(" when ");
            context.getRequires().accept(this);
        }
        if (context.getEnsures() != null) {
            indenter.write(" ensures ");
            context.getEnsures().accept(this);
        }
        context.getAttributes().accept(this);
        indenter.endLine();
        indenter.endLine();
        postpare();
    }

    @Override
    public void visit(LiterateDefinitionComment literateDefinitionComment) {
        prepare(literateDefinitionComment);
        // indenter.write(literateDefinitionComment.getValue());
        // indenter.endLine();
        postpare();
    }

    @Override
    public void visit(Require require) {
        prepare(require);
        if (!forEquivalence) {
            indenter.write("require \"" + require.getValue() + "\"");
            indenter.endLine();
        }
        postpare();
    }

    @Override
    public void visit(BackendTerm term) {
        prepare(term);
        indenter.write(term.getValue());
        postpare();
    }

    @Override
    public void visit(Bracket br) {
        prepare(br);
        indenter.write("(");
        br.getContent().accept(this);
        indenter.write(")");
        postpare();
    }

    @Override
    public void visit(Cast c) {
        prepare(c);
        c.getContent().accept(this);
        indenter.write(" :");
        if (c.isSyntactic()) {
            indenter.write(":");
        }
        indenter.write(c.getSort());
        postpare();
    }

    @Override
    public void visit(Token t) {
        prepare(t);
        indenter.write("#token(\"" + t.tokenSort() + "\", \"" + t.value() + "\")");
        postpare();
    }

    protected void prepare(ASTNode astNode) {
        if (!stack.empty()) {
            if (needsParenthesis(stack.peek(), astNode)) {
                indenter.write("(");
            }
        }
        stack.push(astNode);
        if (annotateLocation) {
            astNode.setLocation("(" + indenter.getLineNo() + "," + indenter.getColNo());
        }
    }

    protected void postpare() {
        ASTNode astNode = stack.pop();
        if (!stack.empty()) {
            if (needsParenthesis(stack.peek(), astNode)) {
                indenter.write(")");
            }
        }
        if (annotateLocation) {
            String loc = astNode.getLocation();
            if (!loc.substring(loc.length() - 1).equals(")")) {
                astNode.setLocation(loc + "," + indenter.getLineNo() + "," + indenter.getColNo() + ")");
            }
        }
    }
    
    private List<Terminal> findRightSyntax(String sort){
        
        Production p = context.canonicalBracketForSort.get(sort);
        if (p == null) {
            return new ArrayList<Terminal>();
        } else {
            List<Terminal> terminals = new ArrayList<>();
            for (ProductionItem item : p.getItems()) {
                if (item instanceof Terminal) {
                    terminals.add((Terminal)item);
                }
            }
            return terminals;
        }
    }

    private boolean needsParenthesis(ASTNode upper, ASTNode astNode) {
        if (!addParentheses)
            return false;
        if (astNode instanceof Rewrite) {
            if ((upper instanceof Cell) || (upper instanceof Rule)) {
                return false;
            }
            return true;
        } else if(astNode instanceof TermCons){
            List<Terminal> isRightSyntax = findRightSyntax(((TermCons) astNode).getSort());
            
            if(isRightSyntax.isEmpty()){
                
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
