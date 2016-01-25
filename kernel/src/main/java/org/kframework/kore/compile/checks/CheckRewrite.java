package org.kframework.kore.compile.checks;

import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KRewrite;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * Created by dwightguth on 1/25/16.
 */
public class CheckRewrite {
    private final Set<KEMException> errors;
    private final Module m;

    public CheckRewrite(Set<KEMException> errors, Module m) {
        this.errors = errors;
        this.m = m;
    }

    public void check(Sentence sentence) {
        if (sentence instanceof Rule) {
            check(((Rule) sentence).body());
        }
    }

    private void check(K body) {
        class Holder {
            boolean hasRewrite = false;
            boolean inRewrite = false;
        }
        Holder h = new Holder();
        new VisitK() {
            @Override
            public void apply(KRewrite k) {
                boolean inRewrite = h.inRewrite;
                if (h.inRewrite) {
                    errors.add(KEMException.compilerError("Rewrites are not allowed to be nested.", k));
                }
                h.hasRewrite = true;
                h.inRewrite = true;
                super.apply(k);
                h.inRewrite = inRewrite;
            }
        }.accept(body);
        if (!h.hasRewrite) {
            errors.add(KEMException.compilerError("Rules must have at least one rewrite.", body));
        }
    }
}
