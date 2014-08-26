// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;
import org.kframework.utils.general.GlobalSettings;

/**
 * Evaluates predicates and functions without doing tree traversal.
 *
 * @deprecated This {@link PrePostTransformer}-based implementation for
 *             substitute and evaluate is just too slow; switch to
 *             {@link SubstituteAndEvaluateTransformer} instead
 *
 * @author Traian
 */
@Deprecated
public class LocalEvaluator extends LocalTransformer {

    /**
     * TODO(YilongL): this field needs to be removed; this was added long time
     * ago for test generation; definitely not the right solution
     * <p>
     * The symbolic constraint of the {@code ConstrainedTerm} which contains the
     * terms to be evaluated by this evaluator.
     */
    private final SymbolicConstraint constraint;

    public LocalEvaluator(TermContext context) {
        this(null, context);
    }

    public LocalEvaluator(SymbolicConstraint constraint, TermContext context) {
        super(context);
        this.constraint = constraint;
    }

    public SymbolicConstraint constraint() {
        return constraint;
    }

    private static String TRACE_MSG = "Function evaluation triggered infinite recursion. Trace:";

    @Override
    public ASTNode transform(KItem kItem) {
        try {
            // TODO(YilongL): shall we consider cache evaluation result in certain cases?
            return kItem.resolveFunctionAndAnywhere(false, context);
        } catch (StackOverflowError e) {
            GlobalSettings.kem.registerCriticalError(TRACE_MSG, e);
            throw e; //unreachable
        } catch (KEMException e) {
            e.exception.addTraceFrame(kItem.kLabel().toString());
            throw e;
        }
    }

    @Override
    public ASTNode transform(KItemProjection kItemProjection) {
        return kItemProjection.evaluateProjection();
    }

    @Override
    public ASTNode transform(ListLookup listLookup) {
        return listLookup.evaluateLookup();
    }

    @Override
    public ASTNode transform(ListUpdate listUpdate) {
        return listUpdate.evaluateUpdate();
    }

    @Override
    public ASTNode transform(SetElementChoice setElementChoice) {
        return setElementChoice.evaluateChoice();
    }

    @Override
    public ASTNode transform(SetLookup setLookup) {
        return setLookup.evaluateLookup();
    }

    @Override
    public ASTNode transform(SetUpdate setUpdate) {
        return setUpdate.evaluateUpdate();
    }

    @Override
    public ASTNode transform(MapKeyChoice mapKeyChoice) {
        return mapKeyChoice.evaluateChoice();
    }

    @Override
    public ASTNode transform(MapLookup mapLookup) {
        return mapLookup.evaluateLookup();
    }

    @Override
    public ASTNode transform(MapUpdate mapUpdate) {
        return mapUpdate.evaluateUpdate();
    }

}
