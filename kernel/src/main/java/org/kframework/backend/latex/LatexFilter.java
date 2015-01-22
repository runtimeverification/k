// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.backend.latex;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.kframework.backend.BackendFilter;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.LiterateComment.LiterateCommentType;
import org.kframework.utils.StringUtil;

public class LatexFilter extends BackendFilter {
    public LatexFilter(org.kframework.kil.loader.Context context) {
        super(context);
    }

    public LatexFilter(org.kframework.kil.loader.Context context, String indent) {
        this(context);
        this.indent = indent;
    }

    protected String endl = System.getProperty("line.separator");
    private StringBuilder preamble = new StringBuilder();
    private boolean firstProduction = false;
    private boolean terminalBefore = false;
    private Map<String, String> colors = new HashMap<String, String>();
    private LatexPatternsVisitor patternsVisitor = new LatexPatternsVisitor(context);
    private boolean firstAttribute;
    private boolean hasTitle = false;

    //The indent for a new line at the current position.
    private String indent = "";

    public LinkedList<Boolean> getWantParens() {
        return wantParens;
    }

    private LinkedList<Boolean> wantParens = new LinkedList<Boolean>();
    {
        wantParens.push(Boolean.TRUE);
    }

    public void setResult(StringBuilder result) {
        this.result = result;
    }

    public StringBuilder getPreamble() {
        return preamble;
    }

    private void increaseIndent() {
        indent += "  ";
    }

    private void decreaseIndent() {
        indent = indent.substring(2);
    }

    private void newLine() {
        result.append(endl).append(indent);
    }

    private boolean isOnNewLine() {
        int lastEndl = result.lastIndexOf(endl);
        return  //nested LatexFilter with no new lines yet
                (lastEndl == -1 && result.length() == indent.length())
                //top-level or nested LatexFilter with new lines
                || result.length() == lastEndl + endl.length() + indent.length();
    }

    private void decreaseIndentAndNewLineIfNeeded() {
        if (isOnNewLine()) {
            decreaseIndent();
            result.delete(result.length() - 2, result.length());
        } else {
            decreaseIndent();
            newLine();
        }
    }

    @Override
    public Void visit(Definition def, Void _void) {
        patternsVisitor.visitNode(def);
        result.append("\\begin{kdefinition}" + endl + "\\maketitle" + endl);
        super.visit(def, _void);
        result.append("\\end{kdefinition}" + endl);
        if (!hasTitle) {
            preamble.append("\\title{" + def.getMainModule() + "}" + endl);
            hasTitle = true;
        }
        return null;
    }

    @Override
    public Void visit(PriorityExtended node, Void _void) {
        return null;
    }

    @Override
    public Void visit(PriorityExtendedAssoc node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Module mod, Void _void) {
        if (mod.isPredefined())
            return null;
        result.append("\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl);
        super.visit(mod, _void);
        result.append("\\end{module}" + endl);
        return null;
    }

    @Override
    public Void visit(Syntax syn, Void _void) {
        result.append(endl + "\\begin{syntaxBlock}");
        firstProduction = true;
        increaseIndent();
        super.visit(syn, _void);
        result.append(endl + "\\end{syntaxBlock}");
        decreaseIndent();
        newLine();
        result.append("%");
        newLine();
        return null;
    }

    @Override
    public Void visit(NonTerminal sort, Void _void) {
        result.append("{\\nonTerminal{\\sort{" + StringUtil.latexify(sort.getName()) + "}}}");
                terminalBefore = false;
                return null;
    }

    @Override
    public Void visit(Production p, Void _void) {
        newLine();
        if (firstProduction) {
            result.append("\\syntax");
            firstProduction = false;
        } else {
            result.append("\\syntaxCont");
        }
      increaseIndent();
      newLine();
      result.append("{");
        if (!(p.getItems().get(0) instanceof UserList)
                && patternsVisitor.getPatterns().containsKey(p)) {
            String pattern = patternsVisitor.getPatterns().get(p);
            int n = 1;
            LatexFilter termFilter = new LatexFilter(context, indent);
            for (ProductionItem pi : p.getItems()) {
                if (!(pi instanceof Terminal)) {
                    termFilter.setResult(new StringBuilder());
                    termFilter.visitNode(pi);
                    pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
                }
            }
            result.append(pattern);
        } else {
            super.visit(p, _void);
        }
        result.append("}");
        newLine();
        result.append("{");
        this.visitNode(p.getAttributes());
        result.append("}");
        decreaseIndent();
        return null;
    }

    @Override
    public Void visit(Terminal pi, Void _void) {
        String terminal = pi.getTerminal();
        if (terminal.isEmpty())
            return null;
        if (context.isSpecialTerminal(terminal)) {
            result.append(StringUtil.latexify(terminal));
        } else {
                  if (terminalBefore) result.append("{}");
            result.append("\\terminal{" + StringUtil.latexify(terminal) + "}");
        }
        terminalBefore = true;
        return null;
    }

    @Override
    public Void visit(UserList ul, Void _void) {
        result.append("List\\{");
        this.visitNode(new NonTerminal(ul.getSort()));
        result.append(", \\mbox{``}" + StringUtil.latexify(ul.getSeparator()) + "\\mbox{''}\\}");
        terminalBefore = false;
        return null;
    }

        @Override
        public Void visit(Lexical t, Void _void) {
                result.append("Token\\{");
                result.append(StringUtil.latexify(t.getLexicalRule()) +  "\\}");
                return null;
        }

    @Override
    public Void visit(Configuration conf, Void _void) {
        result.append("\\kconfig{");
        super.visit(conf, _void);
        result.append("}" + endl);
        return null;
    }

    @Override
    public Void visit(Cell c, Void _void) {
        if(!isOnNewLine()) {
            newLine();
        }
        wantParens.push(Boolean.FALSE);
        Ellipses ellipses = c.getEllipses();
        if (ellipses == Ellipses.LEFT) {
            result.append("\\ksuffix");
        } else if (ellipses == Ellipses.RIGHT) {
            result.append("\\kprefix");
        } else if (ellipses == Ellipses.BOTH) {
            result.append("\\kmiddle");
        } else {
            result.append("\\kall");
        }
        if (c.getCellAttributes().containsKey("color")) {
            colors.put(c.getLabel(), c.getCellAttributes().get("color"));
        }
        if (colors.containsKey(c.getLabel())) {
            result.append("[" + colors.get(c.getLabel()) + "]");
        }
        result.append("{" + StringUtil.latexify(
                c.getLabel() + StringUtil.emptyIfNull(c.getCellAttributes().get("multiplicity"))));
        result.append("}");

        result.append("{");
        increaseIndent();
        newLine();
        super.visit(c, _void);
        decreaseIndentAndNewLineIfNeeded();
        result.append("}");
        wantParens.pop();
        return null;
    }

    public Void visit(Collection col, Void _void) {
        final boolean parens = wantParens.peek();
        final boolean hasBR = containsBR(col);
        if (col.isEmpty()) {
            printEmpty(col.getSort().getName());
            return null;
        }
        if (hasBR) {
            if (!isOnNewLine()) {
                newLine();
            }
            result.append("\\begin{array}{@{}c@{}}");
            increaseIndent();
        }
        List<Term> contents = col.getContents();
        printList(contents, "\\mathrel{}", true);
        if (hasBR) {
            decreaseIndent();
            newLine();
            result.append("\\end{array}");
        }
        return null;
    }

    private boolean containsBR(Collection col) {
        for (Term t : col.getContents()) {
            if (t instanceof TermComment) {
                return true;
            }
        }
        return false;
    }

    private void printList(List<Term> contents, String str, boolean addNewLine) {
        boolean first = true;
        for (Term trm : contents) {
            if (first) {
                first = false;
            } else {
                if (addNewLine && !isOnNewLine()) {
                    newLine();
                }
                result.append(str);
            }
            this.visitNode(trm);
        }
    }

    public Void visit(TermComment tc, Void _void) {
        // termComment = true;
        result.append("\\\\");
        super.visit(tc, _void);
        return null;
    }

    @Override
    public Void visit(Variable var, Void _void) {
        if (var.getName().equals(MetaK.Constants.anyVarSymbol)) {
            result.append("\\AnyVar");
        } else {
            result.append("\\variable");
        }
        if (var.getSort() != null) {
            result.append("[" + StringUtil.latexify(var.getSort().getName()) + "]");
        }
        if (!var.getName().equals(MetaK.Constants.anyVarSymbol)) {
            result.append("{" + makeIndices(makeGreek(StringUtil.latexify(var.getName()))) + "}");
        }
        result.append("{");
        if (var.isUserTyped()) {
            result.append("user");
        }
        result.append("}");
        return null;
    }

    private String makeIndices(String str) {
        return str;
    }

    private String makeGreek(String name) {
        return name.replace("Alpha", "{\\alpha}").replace("Beta", "{\\beta}").replace("Gamma", "{\\gamma}").replace("Delta", "{\\delta}").replace("VarEpsilon", "{\\varepsilon}")
                .replace("Epsilon", "{\\epsilon}").replace("Zeta", "{\\zeta}").replace("Eta", "{\\eta}").replace("Theta", "{\\theta}").replace("Kappa", "{\\kappa}").replace("Lambda", "{\\lambda}")
                .replace("Mu", "{\\mu}").replace("Nu", "{\\nu}").replace("Xi", "{\\xi}").replace("Pi", "{\\pi}").replace("VarRho", "{\\varrho}").replace("Rho", "{\\rho}")
                .replace("VarSigma", "{\\varsigma}").replace("Sigma", "{\\sigma}").replace("GAMMA", "{\\Gamma}").replace("DELTA", "{\\Delta}").replace("THETA", "{\\Theta}")
                .replace("LAMBDA", "{\\Lambda}").replace("XI", "{\\Xi}").replace("PI", "{\\Pi}").replace("SIGMA", "{\\Sigma}").replace("UPSILON", "{\\Upsilon}").replace("PHI", "{\\Phi}");
    }

    @Override
    public Void visit(ListTerminator e, Void _void) {
        printEmpty(e.getSort().getName());
        return null;
    }

    private void printEmpty(String sort) {
        result.append("\\dotCt{" + sort + "}");
    }

    @Override
    public Void visit(Rule rule, Void _void) {
        // termComment = false;
        result.append("\\krule");
        if (!"".equals(rule.getLabel())) {
            result.append("[" + rule.getLabel() + "]");
        }
        result.append("{");
        increaseIndent();
        increaseIndent();
        newLine();
        this.visitNode(rule.getBody());
        decreaseIndentAndNewLineIfNeeded();
        result.append("}");
        newLine();
        result.append("{");
        if (rule.getRequires() != null) {
            this.visitNode(rule.getRequires());
        }
        result.append("}{");
        if (rule.getEnsures() != null) {
            this.visitNode(rule.getEnsures());
        }
        result.append("}{");
        this.visitNode(rule.getAttributes());
        result.append("}");
        result.append("{");
        // if (termComment) result.append("large");
        result.append("}");
        decreaseIndent();
        newLine();
        result.append("%");
        newLine();
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context cxt, Void _void) {
        result.append("\\kcontext");
        result.append("{");
        increaseIndent();
        increaseIndent();
        newLine();
        this.visitNode(cxt.getBody());
        decreaseIndentAndNewLineIfNeeded();
        result.append("}");
        newLine();
        result.append("{");
        if (cxt.getRequires() != null) {
            this.visitNode(cxt.getRequires());
        }
        result.append("}{");
        if (cxt.getEnsures() != null) {
            this.visitNode(cxt.getEnsures());
        }
        result.append("}{");
        this.visitNode(cxt.getAttributes());
        result.append("}");
        decreaseIndent();
        newLine();
        result.append("%");
        newLine();
        return null;
    }

    @Override
    public Void visit(Hole hole, Void _void) {
        result.append("\\khole{}");
        return null;
    }

    @Override
    public Void visit(Rewrite rew, Void _void) {
        wantParens.push(Boolean.TRUE);
        if (!isOnNewLine()) {
            newLine();
        }
        result.append("\\reduce");
        increaseIndent();
        newLine();
        result.append("{");
        this.visitNode(rew.getLeft());
        result.append("}");
        newLine();
        result.append("{");
        this.visitNode(rew.getRight());
        result.append("}");
        decreaseIndent();
        newLine();
        wantParens.pop();
        return null;
    }

    @Override
    public Void visit(Bracket trm, Void _void) {
        if (trm.getContent() instanceof Rewrite)
            super.visit(trm, _void);
        else {
            String pattern = "\\left({#1}\\right)";
            LatexFilter termFilter = new LatexFilter(context, indent);
            termFilter.getWantParens().push(Boolean.FALSE);
            termFilter.visitNode(trm.getContent());
            pattern = pattern.replace("{#1}", "{" + termFilter.getResult() + "}");
            result.append(pattern);
        }
        return null;
    }

    @Override
    public Void visit(TermCons trm, Void _void) {
        String pattern = patternsVisitor.getPatterns().get(trm.getProduction());
        if (pattern == null) {
            Production pr = trm.getProduction();
            patternsVisitor.visitNode(pr);
            pattern = patternsVisitor.getPatterns().get(trm.getProduction());
        }
        int n = 1;
        LatexFilter termFilter = new LatexFilter(context, indent);
        for (Term t : trm.getContents()) {
            termFilter.setResult(new StringBuilder());
            termFilter.visitNode(t);
            pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
        }
        result.append(pattern);
        return null;
    }

        @Override
        public Void visit(KLabelConstant c, Void _void) {
                result.append(StringUtil.latexify(c.getLabel()));
                return null;
        }

    @Override
    public Void visit(Token t, Void _void) {
        result.append("\\constant[" + StringUtil.latexify(t.tokenSort().getName()) + "]{" + StringUtil.latexify(t.value()) + "}");
        return null;
    }

    @Override
    public Void visit(KSequence k, Void _void) {
        if (k.getContents().isEmpty()) printEmpty(Sort.K.getName());
        else printList(k.getContents(), "\\kra", false);
        return null;

    }

    @Override
    public Void visit(KApp app, Void _void) {
        if (app.getLabel() instanceof Token) {
            result.append("\\constant[" + StringUtil.latexify(((Token)app.getLabel()).tokenSort().getName()) + "]{" + StringUtil.latexify(((Token)app.getLabel()).value()) + "}");
        } else {
            this.visitNode(app.getLabel());
            result.append("(");
            this.visitNode(app.getChild());
            result.append(")");
        }
        return null;
    }

    @Override
    public Void visit(KList list, Void _void) {
        printList(list.getContents(), "\\kcomma", false);
        return null;
    }

    @Override
    public Void visit(LiterateDefinitionComment comment, Void _void) {
        if (comment.getType() == LiterateCommentType.LATEX) {
            result.append("\\begin{kblock}[text]" + endl);
            result.append(comment.getValue());
            result.append(endl + "\\end{kblock}" + endl);
            result.append("%");
            newLine();
        } else if (comment.getType() == LiterateCommentType.PREAMBLE) {
            preamble.append(comment.getValue());
            if (comment.getValue().contains("\\title{")) {
                hasTitle = true;
            }
        }
        return null;
    }

    @Override
    public Void visit(LiterateModuleComment comment, Void _void) {
        if (comment.getType() == LiterateCommentType.LATEX) {
            result.append("\\begin{kblock}[text]" + endl);
            result.append(comment.getValue());
            result.append(endl + "\\end{kblock}" + endl);
            result.append("%");
            newLine();
        } else if (comment.getType() == LiterateCommentType.PREAMBLE) {
            preamble.append(comment.getValue());
            if (comment.getValue().contains("\\title{")) {
                hasTitle = true;
            }
        }
        return null;
    }

    @Override
    public Void visit(Attribute entry, Void _void) {
        if (context.isParsingTag(entry.getKey()))
            return null;
        if (entry.getKey().equals(Attribute.keyOf("latex")))
            return null;
        if (entry.getKey().equals(Attribute.keyOf("html")))
            return null;
        if (firstAttribute) {
            firstAttribute = false;
        } else {
            result.append(", ");
        }
        result.append("\\kattribute{" + StringUtil.latexify(entry.getKey().toString()) + "}");
        String value = entry.toString();
        if (!value.isEmpty()) {
            result.append("(" + StringUtil.latexify(value) + ")");
        }
        return null;
    }

    @Override
    public Void visit(Attributes attributes, Void _void) {
        firstAttribute = true;
        for (Attribute<?> entry : attributes.values()) {
            this.visitNode(entry);
        }
        return null;
    }
}
