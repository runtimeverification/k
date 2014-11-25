// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemProjection;
import org.kframework.backend.java.kil.ListUpdate;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.SetUpdate;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.ASTNode;


/**
 * Evaluates pending functions inside a term.
 */
public class Evaluator extends CopyOnWriteTransformer {

    public Evaluator(TermContext context) {
        super(context);
    }

    public static Term evaluate(Term term, TermContext context) {
        Evaluator evaluator = new Evaluator(context);
        return (Term) term.accept(evaluator);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return ((KItem) super.transform(kItem)).resolveFunctionAndAnywhere(false, context);
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        return ((KItemProjection) super.transform(kItemProjection)).evaluateProjection();
    }

    @Override
    public ASTNode transform(ListUpdate listUpdate) {
        return ((ListUpdate) super.transform(listUpdate)).evaluateUpdate();
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        return ((SetUpdate) super.transform(setUpdate)).evaluateUpdate();
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        return ((MapUpdate) super.transform(mapUpdate)).evaluateUpdate();
    }

}
