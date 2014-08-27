// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashMap;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Rewrite;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.LocalTransformer;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.exceptions.ParseFailedException;

/**
 * Do not use outside the parser!
 *
 */
public class CollectVariablesVisitor extends BasicVisitor {
    public CollectVariablesVisitor(Context context) {
        super(context);
    }

    private java.util.Map<String, java.util.List<Variable>> vars = new HashMap<String, java.util.List<Variable>>();

    public java.util.Map<String, java.util.List<Variable>> getVars() {
        return vars;
    }

    public void setVars(java.util.Map<String, java.util.List<Variable>> vars) {
        this.vars = vars;
    }

    @Override
    public Void visit(Cell c, Void _) {
        Sort s = context.getCellSort(c);
        if (s != null)
            try {
                c.setContents((Term) new CollectVariablesVisitor2(context, s).visitNode(c.getContents()));
            } catch (ParseFailedException e) {
                e.printStackTrace();
            }
        return super.visit(c, _);
    }

    @Override
    public Void visit(TermCons node, Void _) {
        if (cache.containsKey(node))
            return null;

        for (int i = 0, j = 0; i < node.getProduction().getItems().size(); i++) {
            if (node.getProduction().getItems().get(i) instanceof NonTerminal) {
                Term t = node.getContents().get(j);
                try {
                    new CollectVariablesVisitor2(context, ((NonTerminal) node.getProduction().getItems().get(i)).getSort()).visitNode(t);
                } catch (ParseFailedException e) {
                    e.printStackTrace();
                }
                this.visitNode(t);
                j++;
            } else if (node.getProduction().getItems().get(i) instanceof UserList) {
                UserList ul = (UserList) node.getProduction().getItems().get(i);
                Term t1 = node.getContents().get(0);
                Term t2 = node.getContents().get(1);
                try {
                    new CollectVariablesVisitor2(context, ul.getSort()).visitNode(t1);
                    new CollectVariablesVisitor2(context, node.getProduction().getSort()).visitNode(t2);
                } catch (ParseFailedException e) {
                    e.printStackTrace();
                }
                this.visitNode(t1);
                this.visitNode(t2);
            }
        }

        return super.visit(node, _);
    }

    @Override
    public Void visit(Variable var, Void _) {
        if (var.getExpectedSort() == null)
            var.setExpectedSort(var.getSort());
        if (!var.getName().equals(MetaK.Constants.anyVarSymbol) && var.isUserTyped()) {
            if (vars.containsKey(var.getName()))
                vars.get(var.getName()).add(var);
            else {
                java.util.List<Variable> varss = new ArrayList<Variable>();
                varss.add(var);
                vars.put(var.getName(), varss);
            }
        }
        return null;
    }

    /**
     * A new class (nested) that goes down one level (jumps over Ambiguity, Rewrite and Bracket) and checks to see if there is a Variable
     *
     * if found, sets a parameter to that variable with the expected sort gathered from the parent production
     *
     * @author Radu
     *
     */
    public class CollectVariablesVisitor2 extends LocalTransformer {
        Sort expectedSort = null;

        public CollectVariablesVisitor2(Context context, Sort expectedSort) {
            super("org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor2", context);
            this.expectedSort = expectedSort;
        }

        @Override
        public ASTNode visit(Variable node, Void _) throws ParseFailedException {
            if (node.isUserTyped()) {
                node.setExpectedSort(node.getSort());
                return node;
            }
            if (node.getExpectedSort() == null) {
                node.setExpectedSort(this.expectedSort);
            }
            // since the terms may be shared, if a node already has an expected sort set up
            // create a new variable with the correct information
            if (!node.getExpectedSort().equals(this.expectedSort)) {
                Variable newV = new Variable(node);
                newV.setExpectedSort(this.expectedSort);
                return newV;
            }
            return node;
        }

        @Override
        public ASTNode visit(Rewrite node, Void _) throws ParseFailedException {
            Rewrite result = new Rewrite(node);
            result.replaceChildren((Term) this.visitNode(node.getLeft()), (Term) this.visitNode(node.getRight()), context);
            return visit((Term) result, _);
        }

        @Override
        public ASTNode visit(Ambiguity node, Void _) throws ParseFailedException {
            ParseFailedException exception = null;
            ArrayList<Term> terms = new ArrayList<Term>();
            for (Term t : node.getContents()) {
                ASTNode result = null;
                try {
                    result = this.visitNode(t);
                    terms.add((Term) result);
                } catch (ParseFailedException e) {
                    exception = e;
                }
            }
            if (terms.isEmpty())
                throw exception;
            if (terms.size() == 1) {
                return terms.get(0);
            }
            node.setContents(terms);
            return visit((Term) node, _);
        }

        @Override
        public ASTNode visit(Bracket node, Void _) throws ParseFailedException {
            node.setContent((Term) this.visitNode(node.getContent()));
            return visit((Term) node, _);
        }
    }
}
