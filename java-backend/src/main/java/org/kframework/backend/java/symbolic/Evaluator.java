// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemProjection;
import org.kframework.backend.java.kil.ListLookup;
import org.kframework.backend.java.kil.ListUpdate;
import org.kframework.backend.java.kil.MapKeyChoice;
import org.kframework.backend.java.kil.MapLookup;
import org.kframework.backend.java.kil.MapUpdate;
import org.kframework.backend.java.kil.SetElementChoice;
import org.kframework.backend.java.kil.SetLookup;
import org.kframework.backend.java.kil.SetUpdate;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.kil.ASTNode;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;


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

    private static String TRACE_MSG = "Function evaluation triggered infinite recursion. Trace:";

    @Override
    public ASTNode transform(KItem kItem) {
        try {
            return ((KItem) super.transform(kItem)).resolveFunctionAndAnywhere(false, context);
        } catch (StackOverflowError e) {
            throw KExceptionManager.criticalError(TRACE_MSG, e);
        } catch (KEMException e) {
            e.exception.addTraceFrame(kItem.kLabel().toString());
            throw e;
        }
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        return ((KItemProjection) super.transform(kItemProjection)).evaluateProjection();
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        return ((ListLookup) super.transform(listLookup)).evaluateLookup();
    }

    @Override
    public ASTNode transform(ListUpdate listUpdate) {
        return ((ListUpdate) super.transform(listUpdate)).evaluateUpdate();
    }

    @Override
    public ASTNode transform(SetElementChoice setElementChoice) {
        return ((SetElementChoice) super.transform(setElementChoice)).evaluateChoice();
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        return ((SetLookup) super.transform(setLookup)).evaluateLookup();
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        return ((SetUpdate) super.transform(setUpdate)).evaluateUpdate();
    }

    @Override
    public ASTNode transform(MapKeyChoice mapKeyChoice) {
        return ((MapKeyChoice) super.transform(mapKeyChoice)).evaluateChoice();
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        return ((MapLookup) super.transform(mapLookup)).evaluateLookup();
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        return ((MapUpdate) super.transform(mapUpdate)).evaluateUpdate();
    }

}
