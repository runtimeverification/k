// Copyright (c) 2020 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KAs;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

import static org.kframework.kore.KORE.*;

import java.util.Set;

public class CheckK {

    private final Set<KEMException> errors;

    public CheckK(Set<KEMException> errors) {
        this.errors = errors;
    }

    private void check(K k) {
        new VisitK() {
            @Override
            public void apply(KAs as) {
                if (!(as.alias() instanceof KVariable)) {
                    errors.add(KEMException.compilerError("Found #as pattern where the right side is not a variable.", as));
                }
                super.apply(as);
            }
        }.apply(k);
    }

    public void check(Sentence s) {
        if (s instanceof Rule) {
            Rule r = (Rule)s;
            check(r.body());
            check(r.requires());
            check(r.ensures());
        } else if (s instanceof Context) {
            Context c = (Context)s;
            check(c.body());
            check(c.requires());
        } else if (s instanceof ContextAlias) {
            ContextAlias c = (ContextAlias)s;
            check(c.body());
            check(c.requires());
        }
    }
}
