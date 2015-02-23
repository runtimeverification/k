// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.awt.Color;
import java.util.Comparator;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

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
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.Definition;
import org.kframework.kil.DefinitionItem;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KItemProjection;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KLabelInjection;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.Location;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Require;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.Token;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.NonCachingVisitor;
import org.kframework.krun.ColorSetting;
import org.kframework.utils.ColorUtil;

import com.davekoelle.AlphanumComparator;

/**
 * Unparses (ie converts an AST to text) a term written in concrete syntax.
 * Provides two methods: {@link #print} and {@link #compare}.
 * @author dwightguth
 *
 */
public class Unparser implements Comparator<ASTNode> {

    public Unparser(Context context) {
        this(context, ColorSetting.OFF, Color.BLACK, true, false);
    }

    public Unparser(Context context, ColorSetting color, Color terminalColor, boolean wrap, boolean annotateLocation) {
        this.context = context;
        this.color = color;
        this.terminalColor = terminalColor;
        this.wrap = wrap;
        this.annotateLocation = annotateLocation;
    }

    private final AlphanumComparator comparator = new AlphanumComparator();
    private final Context context;
    private final ColorSetting color;
    private final Color terminalColor;
    private final boolean wrap;
    private final boolean annotateLocation;
    private Set<String> variableList = new HashSet<>();

    /**
     * Compares the textual representation of two terms.
     *
     *
     * This method is implemented by creating a
     * list of term components consisting of the terminal
     * and non-terminal components of the terms involved.
     * The nonterminals are iteratively resolved when they
     * reach the top of the list, and strings at the top
     * of the list are appended to the textual representation
     * of the term. Only the common prefix of the two term's textual
     * representation is generated; the first difference
     * encountered halts the algorithm.
     */
    @Override
    public int compare(ASTNode o1, ASTNode o2) {
        Deque<Component> thisStack = new LinkedList<>();
        Deque<Component> thatStack = new LinkedList<>();
        Indenter thisString = new Indenter();
        thisString.setWidth(-1);
        Indenter thatString = new Indenter();
        thatString.setWidth(-1);
        thisStack.push(new TermComponent(o1));
        thatStack.push(new TermComponent(o2));
        int lastIdx = 0;
        while (true) {
            processStack(thisStack, thisString);
            processStack(thatStack, thatString);
            int lim = Math.min(thisString.length(), thatString.length());
            String s1 = thisString.stringBuilder.substring(lastIdx, lim);
            String s2 = thatString.stringBuilder.substring(lastIdx, lim);
            lastIdx = lim;
            int result = comparator.compare(s1, s2);
            if (result != 0) return result;
            if (thisStack.isEmpty() && thatStack.isEmpty()) {
                return comparator.compare(thisString.stringBuilder.substring(lim), thatString.stringBuilder.substring(lim));
            }
        }
    }

    /**
     * Outputs the textual representation of a term.
     *
     * This method is implemented by creating a
     * list of term components consisting of the terminal
     * and non-terminal components of the term involved.
     * The nonterminals are iteratively resolved when they
     * reach the top of the list, and strings at the top
     * of the list are appended to the textual representation
     * of the term. When the queue is empty, the resulting
     * string is returned.
     */
    public String print(ASTNode node) {
        Deque<Component> stack = new LinkedList<>();
        Indenter string = new Indenter();
        if (!wrap) {
            string.setWidth(-1);
        }
        stack.push(new TermComponent(node));
        while(!stack.isEmpty()) {
            processStack(stack, string);
        }
        return string.toString();
    }

    /**
     * Pops the top element of the stack and handles it.
     * If it is a string or format character, it is
     * appended to the Indenter. If it is a nonterminal,
     * it computes the components of the corresponding subtertm
     * and adds them to the top of the stack in order.
     */
    private void processStack(Deque<Component> stack, Indenter string) {
        if (stack.isEmpty()) {
            return;
        }
        Component comp = stack.pop();
        if (comp instanceof StringComponent) {
            string.write(((StringComponent)comp).s);
            return;
        }
        if (comp instanceof FormatComponent) {
            FormatComponent format = (FormatComponent) comp;
            switch (format.format) {
            case INDENT:
                string.indent(4);
                break;
            case DEDENT:
                string.unindent();
                break;
            case INDENT_TO_CURRENT:
                string.indentToCurrent();
                break;
            case NEWLINE:
                string.endLine();
                break;
            case END_TERM:
                if (annotateLocation) {
                    format.term.getLocation().lineEnd = string.getLineNo();
                    format.term.getLocation().columnEnd = string.getColNo();
                }
                break;
            }
            return;
        }
        ASTNode term = ((TermComponent) comp).term;
        if (annotateLocation) {
            term.setLocation(new Location(string.getLineNo(), string.getColNo(), 0, 0));
        }
        ComponentVisitor visitor = new ComponentVisitor(context);
        visitor.visitNode(term);
        stack.push(new FormatComponent(Format.END_TERM, term));
        while(!visitor.getStack().isEmpty()) {
            stack.push(visitor.getStack().pollLast());
        }
    }

    private static interface Component {}

    /**
     * A terminal component of the output string: ie, a literal
     * string contained in the output.
     *
     */
    private static class StringComponent implements Component {

        private final String s;

        public StringComponent(String s) {
            this.s = s;
        }

        @Override
        public String toString() {
            return s;
        }
    }

    /**
     * A nonterminal component of the output string. This
     * forms an intermediate representation that is iteratively
     * resolved according to the production corresponding to the
     * term contained at that location in the AST.
     * @author dwightguth
     *
     */
    private static class TermComponent implements Component {
        private final ASTNode term;

        public TermComponent(ASTNode term) {
            this.term = term;
        }

        @Override
        public String toString() {
            return term.toString();
        }
    }

    private static enum Format {
        INDENT, DEDENT, NEWLINE, INDENT_TO_CURRENT, END_TERM
    }

    /**
     * A component of the output string corresponding to a
     * control sequence. This handles the case of indentation,
     * newlines, as well as the option to annotate the AST
     * with the location of the terms in the resulting AST.
     * @author dwightguth
     *
     */
    private static class FormatComponent implements Component {
        private final Format format;
        private final ASTNode term;

        public FormatComponent(Format format, ASTNode term) {
            this.format = format;
            this.term = term;
        }

        @Override
        public String toString() {
            return format.toString();
        }
    }

    /**
     * Locally visits a term and generatres the {@link Component}s
     * corresponding to that term to be put on the top of the stack.
     * @author dwightguth
     *
     */
    private class ComponentVisitor extends NonCachingVisitor {
        private final Deque<Component> stack= new LinkedList<>();

        public ComponentVisitor(Context context) {
            super(context);
        }

        public Deque<Component> getStack() {
            return stack;
        }

        @Override
        public boolean visitChildren() {
            return false;
        }

        private void string(String s) {
            stack.addLast(new StringComponent(s));
        }

        private void term(ASTNode t) {
            stack.addLast(new TermComponent(t));
        }

        private void format(Format f) {
            stack.addLast(new FormatComponent(f, null));
        }

        @Override
        public Void visit(Definition def, Void _void) {
            for (DefinitionItem item : def.getItems()) {
                term(item);
            }
            return null;
        }

        @Override
        public Void visit(Import imp, Void _void) {
            string("imports " + imp.getName());
            format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(Module mod, Void _void) {
            if (!mod.isPredefined()) {
                string("module " + mod.getName());
                format(Format.NEWLINE);
                format(Format.NEWLINE);
                format(Format.INDENT);
                for (ModuleItem item : mod.getItems()) {
                    term(item);
                }
                format(Format.DEDENT);
                string("endmodule");
                format(Format.NEWLINE);
                format(Format.NEWLINE);
            }
            return null;
        }

        @Override
        public Void visit(Syntax syn, Void _void) {
            string("syntax " + syn.getDeclaredSort().getName());
            format(Format.INDENT_TO_CURRENT);
            if (syn.getPriorityBlocks() != null) {
                string(" ::=");
                for (PriorityBlock pb : syn.getPriorityBlocks()) {
                    term(pb);
                    string("  >");
                }
                stack.pollLast();
            }
            format(Format.DEDENT);
            format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(PriorityBlock priorityBlock, Void _void) {
            if (priorityBlock.getProductions() != null) {
                string(" ");
                for (Production p : priorityBlock.getProductions()){
                    term(p);
                    string("  | ");
                }
                stack.pollLast();
            }
            return null;
        }

        @Override
        public Void visit(Production prod, Void _void) {
            for (int i = 0; i < prod.getItems().size(); ++i) {
                ProductionItem pi = prod.getItems().get(i);
                term(pi);
                if (i != prod.getItems().size() - 1) {
                    string(" ");
                }
            }
            if (!prod.getAttributes().isEmpty()) {
                string(" ");
                string("[");
                term(prod.getAttributes());
                string("]");
            }
            format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(NonTerminal sort, Void _void) {
            string(sort.getName());
            return null;
        }

        @Override
        public Void visit(Terminal terminal, Void _void) {
            string("\"" + terminal.getTerminal() + "\"");
            return null;
        }

        @Override
        public Void visit(UserList userList, Void _void) {
            string("List{" + userList.getSort() + ",\"" + userList.getSeparator() + "\"}");
            return null;
        }

        @Override
        public Void visit(KList listOfK, Void _void) {
            java.util.List<Term> termList = listOfK.getContents();
            for (int i = 0; i < termList.size(); ++i) {
                term(termList.get(i));
                if (i != termList.size() - 1) {
                    string(",, ");
                }
            }
            if (termList.size() == 0) {
                string(".KList");
            }
            return null;
        }

        @Override
        public Void visit(Attributes attributes, Void _void) {
            if (!attributes.isEmpty()) {
                Iterator<Attribute<?>> iter = attributes.values().iterator();
                for (int i = 0; i < attributes.size(); ++i) {
                    term(iter.next());
                    if (i != attributes.size() - 1) {
                        string(", ");
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(Attribute attribute, Void _void) {
            string(attribute.toString());
            return null;
        }

        @Override
        public Void visit(Configuration configuration, Void _void) {
            string("configuration");
            format(Format.NEWLINE);
            format(Format.INDENT);
            term(configuration.getBody());
            format(Format.DEDENT);
            format(Format.NEWLINE);
            format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(Cell cell, Void _void) {
            String colorCode = "";
            Cell declaredCell = context.cells.get(cell.getLabel());
            if (declaredCell != null) {
                String declaredColor = declaredCell.getCellAttributes().get("color");
                if (declaredColor != null) {
                    colorCode = ColorUtil.RgbToAnsi(ColorUtil.colors().get(declaredColor), color, terminalColor);
                    string(colorCode);
                }
            }
            string("<");
            string(cell.getLabel());
            for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
                if (entry.getKey() != "ellipses") {
                    string(" " + entry.getKey() + "=\"" + entry.getValue() + "\"");
                }
            }
            string(">");
            if (cell.hasLeftEllipsis()) {
                string("...");
            }
            format(Format.NEWLINE);
            format(Format.INDENT);
            if (!colorCode.equals("")) {
                string(ColorUtil.ANSI_NORMAL);
            }

            term(cell.getContents());

            string(colorCode);
            format(Format.NEWLINE);
            format(Format.DEDENT);
            if (cell.hasRightEllipsis()) {
                string("...");
            }
            string("</" + cell.getLabel() + ">");
            if (!colorCode.equals("")) {
                string(ColorUtil.ANSI_NORMAL);
            }
            return null;
        }

        @Override
        public Void visit(Variable variable, Void _void) {
            if (variable.isFreshVariable())
                string("?");
            else if (variable.isFreshConstant())
                string("!");
            string(variable.getName());
            if (!variableList.contains(variable.getName())) {
                string(":" + variable.getSort());
                variableList.add(variable.getName());

                if (variable.getAttributes().size() > 0) {
                    string("{");
                    term(variable.getAttributes());
                    string("}");
                }
            }
            return null;
        }

        @Override
        public Void visit(ListTerminator terminator, Void _void) {
            string(terminator.toString());
            return null;
        }

        @Override
        public Void visit(Rule rule, Void _void) {
            string("rule ");
            if (!"".equals(rule.getLabel())) {
                string("[" + rule.getLabel() + "]: ");
            }
            variableList.clear();
            term(rule.getBody());
            if (rule.getRequires() != null) {
                string(" requires ");
                term(rule.getRequires());
            }
            if (rule.getEnsures() != null) {
                string(" ensures ");
                term(rule.getEnsures());
            }
            if (!rule.getAttributes().isEmpty()) {
                string(" ");
                string("[");
                term(rule.getAttributes());
                string("]");
            }
            format(Format.NEWLINE);
            format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(KApp kapp, Void _void) {
            term(kapp.getLabel());
            string("(");
            term(kapp.getChild());
            string(")");
            return null;
        }

        @Override
        public Void visit(KSequence ksequence, Void _void) {
            java.util.List<Term> contents = ksequence.getContents();
            if (!contents.isEmpty()) {
                for (int i = 0; i < contents.size(); i++) {
                    term(contents.get(i));
                    if (i != contents.size() - 1) {
                        string(" ~> ");
                    }
                }
            } else {
                string(".K");
            }
            return null;
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
            Production production = termCons.getProduction();
            if (production.isListDecl()) {
                UserList userList = (UserList) production.getItems().get(0);
                String separator = userList.getSeparator();
                java.util.List<Term> contents = termCons.getContents();
                term(contents.get(0));
                string(separator + " ");
                term(contents.get(1));
            } else {
                int where = 0;
                for (int i = 0; i < production.getItems().size(); ++i) {
                    ProductionItem productionItem = production.getItems().get(i);
                    if (!(productionItem instanceof Terminal)) {
                        Term subterm = termCons.getContents().get(where);
                        if (!isDataStructure(termCons) && isDataStructure(subterm)) {
                            format(Format.NEWLINE);
                            format(Format.INDENT);
                            term(subterm);
                            format(Format.DEDENT);
                        } else {
                            term(subterm);
                        }
                        where++;
                    } else {
                        string(((Terminal) productionItem).getTerminal());
                    }
                    // TODO(YilongL): not sure I can simply remove the following code
                    if (i != production.getItems().size() - 1) {
                        if (isDataStructure(termCons)) {
                            format(Format.NEWLINE);
                        } else {
                            string(" ");
                        }
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(Constant constant, Void _void) {
            string(constant.getValue());
            return null;
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
            term(rewrite.getLeft());
            string(" => ");
            term(rewrite.getRight());
            return null;
        }

        @Override
        public Void visit(KLabelConstant kLabelConstant, Void _void) {
            string(kLabelConstant.getLabel().replaceAll("`", "``").replaceAll("\\(", "`(").replaceAll("\\)", "`)").replaceAll(",", "`,"));
            return null;
        }

        @Override
        public Void visit(Collection collection, Void _void) {
            java.util.List<Term> contents = collection.getContents();
            for (int i = 0; i < contents.size(); ++i) {
                term(contents.get(i));
                if (i != contents.size() - 1) {
                    format(Format.NEWLINE);
                }
            }
            if (contents.size() == 0) {
                string("." + collection.getSort());
            }
            return null;
        }

        @Override
        public Void visit(BagItem bagItem, Void _void) {
            string("BagItem(");
            term(bagItem.getItem());
            string(")");
            return null;
        }

        @Override
        public Void visit(Hole hole, Void _void) {
            string("HOLE");
            return null;
        }

        @Override
        public Void visit(FreezerHole hole, Void _void) {
            string("HOLE(" + hole.getIndex() + ")");
            return null;
        }

        @Override
        public Void visit(Freezer freezer, Void _void) {
            term(freezer.getTerm());
            return null;
        }

        @Override
        public Void visit(KInjectedLabel kInjectedLabel, Void _void) {
            Term term = kInjectedLabel.getTerm();
            if (term.getSort().isKSort()) {
                string(KInjectedLabel.getInjectedSort(term.getSort()).getName());
                string("2KLabel ");
            } else {
                string("# ");
            }
            term(term);
            return null;
        }

        @Override
        public Void visit(TermComment termComment, Void _void) {
            string("<br/>");
            return null;
        }

        @Override
        public Void visit(Bag bag, Void _void) {
            boolean first = true;
            for (Term t : bag.getContents()) {
                if (!first) format(Format.NEWLINE);
                term(t);
                first = false;
            }
            return null;
        }

        @Override
        public Void visit(org.kframework.kil.Ambiguity ambiguity, Void _void) {
            string("amb(");
            format(Format.NEWLINE);
            format(Format.INDENT);
            java.util.List<Term> contents = ambiguity.getContents();
            for (int i = 0; i < contents.size(); ++i) {
                term(contents.get(i));
                if (i != contents.size() - 1) {
                    string(",");
                    format(Format.NEWLINE);
                }
            }
            format(Format.NEWLINE);
            format(Format.DEDENT);
            string(")");
            return null;
        }

        @Override
        public Void visit(org.kframework.kil.Context context, Void _void) {
            string("context ");
            variableList.clear();
            term(context.getBody());
            if (context.getRequires() != null) {
                string(" requires ");
                term(context.getRequires());
            }
            if (context.getEnsures() != null) {
                string(" ensures ");
                term(context.getEnsures());
            }
            if (!context.getAttributes().isEmpty()) {
                string(" ");
                string("[");
                term(context.getAttributes());
                string("]");
            }
            format(Format.NEWLINE);
            format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(LiterateDefinitionComment literateDefinitionComment, Void _void) {
            // string(literateDefinitionComment.getValue());
            // format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(Require require, Void _void) {
            string("require \"" + require.getValue() + "\"");
            format(Format.NEWLINE);
            return null;
        }

        @Override
        public Void visit(BackendTerm term, Void _void) {
            string(term.getValue());
            return null;
        }

        @Override
        public Void visit(Bracket br, Void _void) {
            string("(");
            term(br.getContent());
            string(")");
            return null;
        }

        @Override
        public Void visit(Cast c, Void _void) {
            term(c.getContent());
            string(" :");
            if (c.isSyntactic()) {
                string(":");
            }
            string(c.getSort().getName());
            if (c.getAttributes().size() > 0) {
                string("{");
                term(c.getAttributes());
                string("}");
            }
            return null;
        }

        @Override
        public Void visit(Token t, Void _void) {
            string("#token(\"" + t.tokenSort() + "\", \"" + t.value() + "\")");
            return null;
        }

        @Override
        public Void visit(ListBuiltin node, Void p) throws RuntimeException {
            for (Term t : node.elementsLeft()) {
                term(t);
            }
            for (Term t : node.baseTerms()) {
                term(t);
            }
            for (Term t : node.elementsRight()) {
                term(t);
            }
            return null;
        }

        @Override
        public Void visit(MapBuiltin node, Void p) throws RuntimeException {
            for (Map.Entry<Term, Term> entry : node.elements().entrySet()) {
                term(entry.getKey());
                term(entry.getValue());
            }
            for (Term t : node.baseTerms()) {
                term(t);
            }
            return null;
        }

        @Override
        public Void visit(SetBuiltin node, Void p) throws RuntimeException {
            for (Term t : node.elements()) {
                term(t);
            }
            for (Term t : node.baseTerms()) {
                term(t);
            }
            return null;
        }

        @Override
        public Void visit(KItemProjection node, Void p) throws RuntimeException {
            term(node.getTerm());
            return null;
        }

        @Override
        public Void visit(KLabelInjection node, Void p) throws RuntimeException {
            term(node.getTerm());
            return null;
        }
    }
}