// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.kframework.kil.*;
import org.kframework.kil.Cast.CastType;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.krun.ColorSetting;
import org.kframework.parser.TermLoader;

import java.util.HashMap;
import java.util.Map;

public class AddBracketsFilter2 extends ParseForestTransformer {

    private final TermLoader loader;

    public AddBracketsFilter2(Context context, TermLoader loader) {
        super("Add more brackets", context);
        this.loader = loader;
    }

    private Term reparsed = null;
    private AddBracketsFilter2(Term reparsed, Context context, TermLoader loader) {
        super("Add brackets to term based on parse forest", context);
        this.loader = loader;
        this.reparsed = reparsed;
    }

    public Map<String, Term> substitution = new HashMap<String, Term>();
    private boolean atTop = true;

    @Override
    public ASTNode visit(TermCons ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(Constant ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(Collection ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(Cell ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(CollectionItem ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(KApp ast, Void _) throws ParseFailedException {
        if (ast.getLabel() instanceof Token) return ast;
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(Hole ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(Freezer ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    @Override
    public ASTNode visit(KInjectedLabel ast, Void _) throws ParseFailedException {
        boolean tmp = atTop;
        atTop = false;
        ASTNode result = super.visit(ast, _);
        return postpare((Term)result, tmp);
    }

    private ASTNode postpare(Term ast, boolean atTop) throws ParseFailedException {
        if (reparsed != null) {
            ASTNode result = addBracketsIfNeeded(ast);
            if (atTop && result instanceof Bracket) {
                return new Cast(result.getLocation(), result.getSource(), (Term)result, CastType.SYNTACTIC, context);
            }
            return result;
        }
        UnparserFilter unparser = new UnparserFilter(false, ColorSetting.OFF, OutputModes.SMART, true, context);
        unparser.visitNode(ast);
        String unparsed = unparser.getResult();
        try {
            ASTNode rule = loader.parsePatternAmbiguous(unparsed, context);
            Term reparsed = ((Sentence)rule).getBody();
            if (!reparsed.contains(ast)) {
                return replaceWithVar(ast);
            }
            return new AddBracketsFilter2(reparsed, context, loader).visitNode(ast);
        } catch (ParseFailedException e) {
            return replaceWithVar(ast);
        }
    }

    private Variable replaceWithVar(Term ast) {
        Variable var = Variable.getAnonVar(((Term)ast).getSort());
        substitution.put(var.getName(), (Term) ast);
        return var;
    }

    private ASTNode addBracketsIfNeeded(Term ast) throws ParseFailedException {
        TraverseForest trans = new TraverseForest(ast, context);
        reparsed = (Term) trans.visitNode(reparsed);
        if (trans.needsParens) {
            return new Bracket(ast.getLocation(), ast.getSource(), ast, context);
        }
        return ast;
    }

    private class TraverseForest extends ParseForestTransformer {
        public TraverseForest(Term ast, org.kframework.kil.loader.Context context) {
            super("Determine if term needs parentheses", context);
            this.ast = ast;
        }
        private Term ast;
        public boolean needsParens;
        private boolean hasTerm;
        private Location realLocation;

        public ASTNode visit(Ambiguity amb, Void _) throws ParseFailedException {
            realLocation = ast.getLocation();
            for (int i = amb.getContents().size() - 1; i >= 0; i--) {
                Term t = amb.getContents().get(i);
                boolean tmp = hasTerm;
                hasTerm = false;
                this.visitNode(t);
                if (!hasTerm) {
                    needsParens = true;
                    amb.getContents().remove(i);
                }
                hasTerm = tmp;

            }
            if (amb.getContents().size() == 1)
                return amb.getContents().get(0);
            return amb;
        }

        public ASTNode visit(Term t, Void _) throws ParseFailedException {
            if (t.equals(ast) && t.getLocation().equals(realLocation)) {
                hasTerm = true;
            }
            return t;
        }
    }
}
