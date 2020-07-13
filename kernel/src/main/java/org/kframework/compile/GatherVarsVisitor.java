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
    private final Set<KEMException> errors;
    private final boolean errorExistential;

    public GatherVarsVisitor(boolean isBody, Set<KEMException> errors, Set<KVariable> vars, boolean errorExistential) {
        super(isBody, errors);
        this.errors = errors;
        this.vars = vars;
        this.errorExistential = errorExistential;
    }

    @Override
    public void apply(KVariable v) {
        if (isLHS() && !ResolveAnonVar.isAnonVar(v))
            vars.add(v);
        if (errorExistential && v.name().startsWith("?")) {
            errors.add(KEMException.compilerError("Found existential variable not supported by concrete backend.", v));
        }
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
