// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.Substitution;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.*;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ResolveFresh extends CopyOnWriteTransformer {

    private boolean isFresh;
    private Set<Variable> vars = new HashSet<Variable>();

    public ResolveFresh(Context context) {
        super("Resolve fresh variables condition.", context);
    }

    @Override
    public ASTNode visit(Definition node, Void _)  {
        isFresh = false;
        node = (Definition) super.visit(node, _);
        if (!isFresh)
            return node;

        Configuration cfg = MetaK.getConfiguration(node, context);
        Bag bag;
        if (cfg.getBody() instanceof Bag) {
            bag = (Bag) cfg.getBody().shallowCopy();
        } else {
            bag = new Bag();
            bag.getContents().add(cfg.getBody());
        }
        cfg.setBody(bag);

        Cell nId = new Cell();
        nId.setLabel("freshCounter");
        nId.setEllipses(Ellipses.NONE);
        nId.setContents(IntBuiltin.ZERO);
        bag.getContents().add(nId);

        return node;
    }

    @Override
    public ASTNode visit(Sentence node, Void _)  {
        //TODO: maybe now fresh should be in the ensures part.
        if (null == node.getRequires())
            return node;

        vars.clear();
        ASTNode condNode = this.visitNode(node.getRequires());
        if (vars.isEmpty())
            return node;

        node = node.shallowCopy();
        node.setRequires((Term) condNode);
        Variable freshVar = Variable.getFreshVar("Int");
        ASTNode bodyNode = freshSubstitution(vars, freshVar).visitNode(node.getBody());
        assert(bodyNode instanceof Term);
        Bag bag;
        if (bodyNode instanceof Bag) {
            bag = (Bag) bodyNode;
        } else {
            bag = new Bag();
            bag.getContents().add((Term)bodyNode);
        }
        node.setBody(bag);

        Cell fCell = new Cell();
        fCell.setLabel("freshCounter");
        fCell.setEllipses(Ellipses.NONE);
        TermCons t = new TermCons("Int", "Int1PlusSyn", context);
        t.getContents().add(freshVar);
        t.getContents().add(IntBuiltin.kAppOf(vars.size()));
        fCell.setContents(new Rewrite(freshVar, t, context));
        bag.getContents().add(fCell);

        return node;
    }

    @Override
    public ASTNode visit(TermCons node, Void _)  {
        if (MetaK.Constants.freshCons.equals(node.getCons())) {
            assert(1 == node.getContents().size());
            assert(node.getContents().get(0) instanceof Variable);

            Variable var = (Variable) node.getContents().get(0);
            this.vars.add(var);
            this.isFresh = true;
            return BoolBuiltin.TRUE;
        }

        return super.visit(node, _);
    }

    private Substitution freshSubstitution(
            Set<Variable> vars,
            Variable idxVar) {
        Map<Term, Term> symMap = new HashMap<Term, Term>();
        int idx = 0;
        for (Variable var : vars) {
            TermCons idxTerm = new TermCons("Int", MetaK.Constants.plusIntCons, context);
            List<Term> subterms = idxTerm.getContents();
            subterms.add(idxVar);
            subterms.add(IntBuiltin.kAppOf(idx));
            ++idx;

            String sort = var.getSort();
            Term symTerm = new AddSymbolicK(context).makeSymbolicTerm(sort, idxTerm);
            symMap.put(var, symTerm);
        }

        return new Substitution(symMap, context);
    }

}

