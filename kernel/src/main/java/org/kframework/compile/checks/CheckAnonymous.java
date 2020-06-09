package org.kframework.compile.checks;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;
import org.kframework.attributes.Att;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;

import static org.kframework.kore.KORE.*;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

public class CheckAnonymous {

    private final Set<KEMException> errors;
    private final KExceptionManager kem;
    private final Module module;

    public CheckAnonymous(Set<KEMException> errors, Module module, KExceptionManager kem) {
        this.errors = errors;
        this.kem = kem;
        this.module = module;
    }

    private final Multiset<String> vars = HashMultiset.create();
    private final Map<String, K> loc = new HashMap<>();

    private void resetVars() {
        vars.clear();
        loc.clear();
    }

    private void gatherVars(K k) {
        new VisitK() {
            @Override
            public void apply(KVariable var) {
              vars.add(var.name());
              loc.put(var.name(), var);
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
            }
        }.apply(k);
    }

    public void check(Sentence s) {
        if (s.att().getOptional(Att.LABEL()).orElse("").equals("STDIN-STREAM.stdinUnblock")) {
            return;
        }
        resetVars();
        if (s instanceof Rule) {
            Rule r = (Rule)s;
            gatherVars(r.body());
            gatherVars(r.requires());
            gatherVars(r.ensures());
        } else if (s instanceof Context) {
            Context c = (Context)s;
            gatherVars(c.body());
            gatherVars(c.requires());
        } else if (s instanceof ContextAlias) {
            ContextAlias c = (ContextAlias)s;
            gatherVars(c.body());
            gatherVars(c.requires());
        }
        for (Multiset.Entry<String> entry : vars.entrySet()) {
            if (entry.getCount() == 1) {
                if (!(ResolveAnonVar.isAnonVar(KVariable(entry.getElement())))) {
                    if (s instanceof ContextAlias && entry.getElement().equals("HERE")) {
                        continue;
                    }
                    if (s instanceof Context && entry.getElement().equals("HOLE")) {
                        continue;
                    }
                    kem.registerCompilerWarning(errors, "Variable '" + entry.getElement() + "' defined but not used.", loc.get(entry.getElement()));
                }
            }
        }
    }
}
