package org.kframework.backend.latex;

import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.StringUtil;

import java.util.HashMap;
import java.util.Map;


public class LatexPatternsVisitor extends BasicVisitor {
    public LatexPatternsVisitor(org.kframework.kil.loader.Context context) {
        super(context);
    }

    private Map<String, String> patterns = new HashMap<String, String>();
    private String pattern = "";
    private int nonTerm;
    private boolean prevNonTerm;

    public Map<String, String> getPatterns() {
        return patterns;
    }

    @Override
    public void visit(Production p) {
        if (!p.containsAttribute("cons")) {
            return;
        }
        if (p.containsAttribute("latex")) {
            pattern = p.getAttribute("latex");
        } else {
            pattern = "";
            nonTerm = 1;
            prevNonTerm = false;
            super.visit(p);
        }
        patterns.put(p.getAttribute("cons"), pattern);
    }

    @Override
    public void visit(Sort sort) {
        if (prevNonTerm)
            pattern += "\\mathrel{}";
        pattern += "{#" + nonTerm++ + "}";
        prevNonTerm = true;
    }

    @Override
    public void visit(UserList sort) {
        // Should be only nonterminal in a production, so prevNonTerm has no effect
        pattern += "{#" + nonTerm++ + "}";
        pattern += "\\mathpunct{\\terminalNoSpace{" + StringUtil.latexify(sort.getSeparator()) + "}}";
        pattern += "{#" + nonTerm++ + "}";
    }

    @Override
    public void visit(Terminal pi) {
        String terminal = pi.getTerminal();
        if (terminal.isEmpty())
            return;
        if (context.isSpecialTerminal(terminal)) {
            pattern += StringUtil.latexify(terminal);
        } else {
                        if (!prevNonTerm) pattern += "{}";
            pattern += "\\terminal{" + StringUtil.latexify(terminal) + "}";
        }
        prevNonTerm = false;
    }

    @Override
    public void visit(Rule node) {
    }

    @Override
    public void visit(Configuration node) {
    }

    @Override
    public void visit(org.kframework.kil.Context node) {
    }
}
