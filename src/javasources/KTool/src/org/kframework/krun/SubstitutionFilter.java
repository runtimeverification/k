// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.*;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.Map;

public class SubstitutionFilter extends CopyOnWriteTransformer {

    private Map<String, Term> args;

    public SubstitutionFilter(Map<String, Term> args, org.kframework.kil.loader.Context context) {
        super("Plug terms into variables", context);
        this.args = args;
    }

    @Override
    public ASTNode visit(Variable var, Void _) {
        Term t = args.get(var.getName());
        if (t == null) {
            t = args.get(var.getName() + ":" + var.getSort());
        }
        if (t == null) {
            GlobalSettings.kem.register(new KException(
                ExceptionType.ERROR,
                KExceptionGroup.CRITICAL,
                "Configuration variable missing: " + var.getName(),
                var.getFilename(), var.getLocation()));
        }
        if (t instanceof BackendTerm) {
            t.setSort(var.getSort());
        }
        return t;
    }
}
