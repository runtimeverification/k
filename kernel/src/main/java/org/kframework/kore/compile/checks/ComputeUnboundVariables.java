package org.kframework.kore.compile.checks;

import org.kframework.builtin.KLabels;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.compile.ResolveAnonVar;
import org.kframework.kore.compile.RewriteAwareVisitor;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;
import java.util.function.Consumer;

/**
 * Created by dwightguth on 3/6/17.
 */
public class ComputeUnboundVariables extends RewriteAwareVisitor {
    private final Set<KVariable> vars;
    private final Consumer<KVariable> reporter;

    public ComputeUnboundVariables(boolean isBody, Set<KEMException> errors, Set<KVariable> vars, Consumer<KVariable> reporter) {
        super(isBody, errors);
        this.vars = vars;
        this.reporter = reporter;
    }

    @Override
    public void apply(KVariable k) {
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
        if (k.klabel() instanceof KVariable) {
            apply((KVariable) k.klabel());
        }
        super.apply(k);
    }
}
