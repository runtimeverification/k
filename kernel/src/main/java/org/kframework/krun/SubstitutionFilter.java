// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.*;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.Map;

public class SubstitutionFilter extends CopyOnWriteTransformer {

    private Map<String, Term> args;

    public SubstitutionFilter(Map<String, Term> args, org.kframework.kil.loader.Context context) {
        super("Plug terms into variables", context);
        this.args = args;
    }

    @Override
    public ASTNode visit(Variable var, Void _void) {
        Term t = args.get(var.getName());
        if (t == null) {
            t = args.get(var.getName() + ":" + var.getSort());
        }
        if (t == null) {
            throw KExceptionManager.criticalError(
                "Configuration variable missing: " + var.getName(),
                this, var);
        }
        if (t instanceof BackendTerm) {
            t.setSort(var.getSort());
        }
        return t;
    }
}
