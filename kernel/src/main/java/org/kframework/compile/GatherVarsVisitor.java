package org.kframework.compile;

import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * Created by dwightguth on 3/6/17.
 */
public class GatherVarsVisitor extends RewriteAwareVisitor {
    private final Set<KVariable> vars;

    public GatherVarsVisitor(boolean isBody, Set<KEMException> errors, Set<KVariable> vars) {
        super(isBody, errors);
        this.vars = vars;
    }

    @Override
    public void apply(KVariable v) {
        if (isLHS() && !v.equals(ResolveAnonVar.ANON_VAR) && !v.equals(ResolveAnonVar.FRESH_ANON_VAR))
            vars.add(v);
        super.apply(v);
    }

    @Override
    public void apply(KApply k) {
        if (k.klabel() instanceof KVariable) {
            apply((KVariable) k.klabel());
        }
        super.apply(k);
    }

    @Override
    public void apply(InjectedKLabel k) {
        if (k.klabel() instanceof KVariable) {
            apply((KVariable) k.klabel());
        }
        super.apply(k);
    }
}
