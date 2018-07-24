// Copyright (c) 2017-2018 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.builtin.KLabels;
import org.kframework.definition.Production;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.compile.RewriteAwareVisitor;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;
import java.util.function.Consumer;

import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 3/6/17.
 */
public class ComputeUnboundVariables extends RewriteAwareVisitor {
    private final Set<KVariable> vars;
    private final Consumer<KVariable> reporter;
    private Sort context = null;

    public ComputeUnboundVariables(boolean isBody, Set<KEMException> errors, Set<KVariable> vars, Consumer<KVariable> reporter) {
        super(isBody, errors);
        this.vars = vars;
        this.reporter = reporter;
    }

    @Override
    public void apply(KVariable k) {
        if (context != null) {
            k = KVariable(k.name(), k.att().add(Sort.class, context));
        }
        if (isRHS()) {
            if (!k.name().equals(KLabels.THIS_CONFIGURATION) &&
                    ((k.equals(ResolveAnonVar.ANON_VAR) && !isLHS())
                            || (!k.equals(ResolveAnonVar.ANON_VAR) && !(k.name().startsWith("?") || k.name().startsWith("!")) && !vars.contains(k)))) {
                reporter.accept(k);
            }
        }
    }

    @Override
    public void apply(InjectedKLabel k) {
        if (k.klabel() instanceof KVariable) {
            apply((KVariable) k.klabel());
        }
        super.apply(k);
    }

    @Override
    public void apply(KApply k) {
        if (k.klabel().name().startsWith("#SemanticCastTo")) {
            Sort savedContext = context;
            context = k.att().get(Production.class).sort();
            apply(k.items().get(0));
            context = savedContext;
            return;
        }
        if (k.klabel() instanceof KVariable) {
            apply((KVariable) k.klabel());
        }
        super.apply(k);
    }
}
