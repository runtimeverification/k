// Copyright (c) 2012-2014 K Team. All Rights Reserved.
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
import org.kframework.kil.loader.*;
import org.kframework.utils.StringUtil;

public class LatexFilter extends BackendFilter {
    public LatexFilter(org.kframework.kil.loader.Context context) {
        super(context);
    }

    protected String endl = System.getProperty("line.separator");
    private StringBuilder preamble = new StringBuilder();
    private boolean firstProduction = false;
    private boolean terminalBefore = false;
    private Map<String, String> colors = new HashMap<String, String>();
    private LatexPatternsVisitor patternsVisitor = new LatexPatternsVisitor(context);
    private boolean firstAttribute;
    private boolean hasTitle = false;

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

    @Override
    public Void visit(Definition def, Void _) {
        patternsVisitor.visitNode(def);
        result.append("\\begin{kdefinition}" + endl + "\\maketitle" + endl);
        super.visit(def, _);
        result.append("\\end{kdefinition}" + endl);
        if (!hasTitle) {
            preamble.append("\\title{" + def.getMainModule() + "}" + endl);
            hasTitle = true;
        }
        return null;
    }

    @Override
    public Void visit(PriorityExtended node, Void _) {
        return null;
    }

    @Override
    public Void visit(PriorityExtendedAssoc node, Void _) {
        return null;
    }

    @Override
    public Void visit(Module mod, Void _) {
        if (mod.isPredefined())
            return null;
        result.append("\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl);
        super.visit(mod, _);
        result.append("\\end{module}" + endl);
        return null;
    }

    @Override
    public Void visit(Syntax syn, Void _) {
        result.append(endl + "\\begin{syntaxBlock}");
        firstProduction = true;
        super.visit(syn, _);
        result.append(endl + "\\end{syntaxBlock}" + endl);
        return null;
    }

    @Override
    public Void visit(Sort sort, Void _) {
        result.append("{\\nonTerminal{\\sort{" + StringUtil.latexify(sort.getName()) + "}}}");
                terminalBefore = false;
                return null;
    }

    @Override
    public Void visit(Production p, Void _) {
        if (firstProduction) {
            result.append("\\syntax{");
            firstProduction = false;
        } else {
            result.append("\\syntaxCont{");
        }
        if (!(p.getItems().get(0) instanceof UserList) && p.containsAttribute(Constants.CONS_cons_ATTR)
                && patternsVisitor.getPatterns().containsKey(p.getAttribute(Constants.CONS_cons_ATTR))) {
            String pattern = patternsVisitor.getPatterns().get(p.getAttribute(Constants.CONS_cons_ATTR));
            int n = 1;
            LatexFilter termFilter = new LatexFilter(context);
            for (ProductionItem pi : p.getItems()) {
                if (!(pi instanceof Terminal)) {
                    termFilter.setResult(new StringBuilder());
                    termFilter.visitNode(pi);
                    pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
                }
            }
            result.append(pattern);
        } else {
            super.visit(p, _);
        }
        result.append("}{");
        this.visitNode(p.getAttributes());
        result.append("}");
        return null;
    }

    @Override
    public Void visit(Terminal pi, Void _) {
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
    public Void visit(UserList ul, Void _) {
        result.append("List\\{");
        this.visitNode(new Sort(ul.getSort()));
        result.append(", \\mbox{``}" + StringUtil.latexify(ul.getSeparator()) + "\\mbox{''}\\}");
        terminalBefore = false;
        return null;
    }

        @Override
        public Void visit(Lexical t, Void _) {
                result.append("Token\\{");
                result.append(StringUtil.latexify(t.getLexicalRule()) +  "\\}");
                return null;
        }

    @Override
    public Void visit(Configuration conf, Void _) {
        result.append("\\kconfig{");
        super.visit(conf, _);
        result.append("}" + endl);
        return null;
    }

    @Override
    public Void visit(Cell c, Void _) {
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
        result.append("{" + StringUtil.latexify(c.getLabel() + StringUtil.emptyIfNull(c.getCellAttributes().get("multiplicity"))) + "}{");
        super.visit(c, _);
        result.append("}" + endl);
        wantParens.pop();
        return null;
    }

    public Void visit(Collection col, Void _) {
        final boolean parens = wantParens.peek();
        final boolean hasBR = containsBR(col);
        if (col.isEmpty()) {
            printEmpty(col.getSort());
            return null;
        }
        if (hasBR) {
            result.append("\\begin{array}{@{}c@{}}");
        }
        List<Term> contents = col.getContents();
        printList(contents, "\\mathrel{}");
        if (hasBR) {
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

    private void printList(List<Term> contents, String str) {
        boolean first = true;
        for (Term trm : contents) {
            if (first) {
                first = false;
            } else {
                result.append(str);
            }
            this.visitNode(trm);
        }
    }

    public Void visit(TermComment tc, Void _) {
        // termComment = true;
        result.append("\\\\");
        super.visit(tc, _);
        return null;
    }

    @Override
    public Void visit(Variable var, Void _) {
        if (var.getName().equals(MetaK.Constants.anyVarSymbol)) {
            result.append("\\AnyVar");
        } else {
            result.append("\\variable");
        }
        if (var.getSort() != null) {
            result.append("[" + StringUtil.latexify(var.getSort()) + "]");
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
    public Void visit(ListTerminator e, Void _) {
        printEmpty(e.getSort());
        return null;
    }

    private void printEmpty(String sort) {
        result.append("\\dotCt{" + sort + "}");
    }

    @Override
    public Void visit(Rule rule, Void _) {
        // termComment = false;
        result.append("\\krule");
        if (!"".equals(rule.getLabel())) {
            result.append("[" + rule.getLabel() + "]");
        }
        result.append("{" + endl);
        this.visitNode(rule.getBody());
        result.append("}{");
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
        result.append(endl);
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context cxt, Void _) {
        result.append("\\kcontext");
        result.append("{" + endl);
        this.visitNode(cxt.getBody());
        result.append("}{");
        if (cxt.getRequires() != null) {
            this.visitNode(cxt.getRequires());
        }
        result.append("}{");
        if (cxt.getEnsures() != null) {
            this.visitNode(cxt.getEnsures());
        }
        result.append("}{");
        this.visitNode(cxt.getAttributes());
        result.append("}" + endl);
        return null;
    }

    @Override
    public Void visit(Hole hole, Void _) {
        result.append("\\khole{}");
        return null;
    }

    @Override
    public Void visit(Rewrite rew, Void _) {
        wantParens.push(Boolean.TRUE);
        result.append("\\reduce{");
        this.visitNode(rew.getLeft());
        result.append("}{");
        this.visitNode(rew.getRight());
        result.append("}");
        wantParens.pop();
        return null;
    }

    @Override
    public Void visit(Bracket trm, Void _) {
        if (trm.getContent() instanceof Rewrite)
            super.visit(trm, _);
        else {
            String pattern = "\\left({#1}\\right)";
            LatexFilter termFilter = new LatexFilter(context);
            termFilter.getWantParens().push(Boolean.FALSE);
            termFilter.visitNode(trm.getContent());
            pattern = pattern.replace("{#1}", "{" + termFilter.getResult() + "}");
            result.append(pattern);
        }
        return null;
    }

    @Override
    public Void visit(TermCons trm, Void _) {
        String pattern = patternsVisitor.getPatterns().get(trm.getCons());
        if (pattern == null) {
            Production pr = context.conses.get(trm.getCons());
            patternsVisitor.visitNode(pr);
            pattern = patternsVisitor.getPatterns().get(trm.getCons());
        }
        int n = 1;
        LatexFilter termFilter = new LatexFilter(context);
        for (Term t : trm.getContents()) {
            termFilter.setResult(new StringBuilder());
            termFilter.visitNode(t);
            pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
        }
        result.append(pattern);
        return null;
    }

        @Override
        public Void visit(KLabelConstant c, Void _) {
                result.append(StringUtil.latexify(c.getLabel()));
                return null;
        }

    @Override
    public Void visit(Token t, Void _) {
        result.append("\\constant[" + StringUtil.latexify(t.tokenSort()) + "]{" + StringUtil.latexify(t.value()) + "}");
        return null;
    }

    @Override
    public Void visit(MapItem mi, Void _) {
        this.visitNode(mi.getKey());
        result.append("\\mapsto");
        this.visitNode(mi.getItem());
        return null;
    }

    @Override
    public Void visit(KSequence k, Void _) {
        if (k.getContents().isEmpty()) printEmpty(KSort.K.name());
        else printList(k.getContents(), "\\kra");
        return null;

    }

    @Override
    public Void visit(KApp app, Void _) {
        if (app.getLabel() instanceof Token) {
            result.append("\\constant[" + StringUtil.latexify(((Token)app.getLabel()).tokenSort()) + "]{" + StringUtil.latexify(((Token)app.getLabel()).value()) + "}");
        } else {
            this.visitNode(app.getLabel());
            result.append("(");
            this.visitNode(app.getChild());
            result.append(")");
        }
        return null;
    }

    @Override
    public Void visit(KList list, Void _) {
        printList(list.getContents(), "\\kcomma");
        return null;
    }

    @Override
    public Void visit(LiterateDefinitionComment comment, Void _) {
        if (comment.getType() == LiterateCommentType.LATEX) {
            result.append("\\begin{kblock}[text]" + endl);
            result.append(comment.getValue());
            result.append("\\end{kblock}" + endl);
        } else if (comment.getType() == LiterateCommentType.PREAMBLE) {
            preamble.append(comment.getValue());
            if (comment.getValue().contains("\\title{")) {
                hasTitle = true;
            }
        }
        return null;
    }

    @Override
    public Void visit(LiterateModuleComment comment, Void _) {
        if (comment.getType() == LiterateCommentType.LATEX) {
            result.append("\\begin{kblock}[text]" + endl);
            result.append(comment.getValue());
            result.append("\\end{kblock}" + endl);
        } else if (comment.getType() == LiterateCommentType.PREAMBLE) {
            preamble.append(comment.getValue());
            if (comment.getValue().contains("\\title{")) {
                hasTitle = true;
            }
        }
        return null;
    }

    @Override
    public Void visit(Attribute entry, Void _) {
        if (Constants.GENERATED_LOCATION.equals(entry.getLocation()))
            return null;
        if (context.isTagGenerated(entry.getKey()))
            return null;
        if (context.isParsingTag(entry.getKey()))
            return null;
        if (entry.getKey().equals("latex"))
            return null;
        if (entry.getKey().equals("html"))
            return null;
        if (firstAttribute) {
            firstAttribute = false;
        } else {
            result.append(", ");
        }
        result.append("\\kattribute{" + StringUtil.latexify(entry.getKey()) + "}");
        String value = entry.getValue();
        if (!value.isEmpty()) {
            result.append("(" + StringUtil.latexify(value) + ")");
        }
        return null;
    }

    @Override
    public Void visit(Attributes attributes, Void _) {
        firstAttribute = true;
        for (Attribute entry : attributes.getContents()) {
            this.visitNode(entry);
        }
        return null;
    }
}
