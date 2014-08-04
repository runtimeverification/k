// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.html;

import org.kframework.kil.Production;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashMap;
import java.util.Map;


public class HTMLPatternsVisitor extends BasicVisitor {
    public HTMLPatternsVisitor(Context context) {
        super(context);
    }

    public enum HTMLPatternType {
        LATEX, HTML, DEFAULT
    };

    private Map<Production,String> patterns = new HashMap<Production,String>();
    private Map<Production,HTMLPatternType> type = new HashMap<Production,HTMLPatternType>();

    String pattern = "";
    int nonTerm;
    boolean prevNonTerm;

    public void setPatterns(Map<Production,String> patterns) {
        this.patterns = patterns;
    }


    public Map<Production,String> getPatterns() {
        return patterns;
    }

    public HTMLPatternType getPatternType(Production prod){
        if(type.containsKey(prod))
            return type.get(prod);
        else
            return null;
    }

    @Override
    public Void visit(Production p, Void _) {
        if(p.containsAttribute("latex") || p.containsAttribute("html")) {
            if (p.containsAttribute("latex")) {

                pattern = p.getAttribute("latex");
                pattern = pattern.replace("\\\\", "\\");
                patterns.put(p, pattern);
                type.put(p, HTMLPatternType.LATEX);

            }
            if (p.containsAttribute("html")) {

                pattern = p.getAttribute("html");
                pattern = pattern.substring(1, pattern.length()-1).replace("\\\\", "\\");
                patterns.put(p, pattern);
                type.put(p, HTMLPatternType.HTML);

            }
        } else {
            type.put(p, HTMLPatternType.DEFAULT);
            //super.visit(p);
        }
        return _;

    }


    @Override
    public Void visit(NonTerminal sort, Void _) {
        return _;
        /*if (prevNonTerm) pattern += "\\mathrel{}";
        pattern += "{#" + nonTerm++ + "}";
        prevNonTerm = true;*/
    }


    @Override
    public Void visit(UserList sort, Void _) {
        return _;
        //Should be only nonterminal in a production, so prevNonTerm has no effect
        /*pattern += "{#" + nonTerm++ + "}";
        pattern += "\\mathpunct{\\terminalNoSpace{" + StringUtil.latexify(sort.getSeparator()) + "}}";
        pattern += "{#" + nonTerm++ + "}";*/
    }


    @Override
    public Void visit(Terminal pi, Void _) {
        return _;
        /*String terminal = pi.getTerminal();
        if (terminal.isEmpty()) return;
        if (context.isSpecialTerminal(terminal)) {
            pattern += StringUtil.latexify(terminal);
        } else {
            pattern += "\\terminal{" + StringUtil.latexify(terminal) + "}";
        }
        prevNonTerm = false;*/
    }

}
