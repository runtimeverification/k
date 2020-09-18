package org.kframework.compile.checks;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.compile.ResolveAnonVar;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static org.kframework.kore.KORE.*;

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
        if (s.att().getOptional(Att.LABEL()).orElse("").equals("STDIN-STREAM.stdinUnblock"))
            return;
        if (s.att().getOptional(Source.class).orElse(Source.apply("")).source().equals("generated"))
            return;
        resetVars();
        if (s instanceof RuleOrClaim) {
            RuleOrClaim r = (RuleOrClaim) s;
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
                if (!(entry.getElement().startsWith("_") || entry.getElement().startsWith("?_") || entry.getElement().startsWith("!_") || entry.getElement().startsWith("@_"))) {
                    if (s instanceof ContextAlias && entry.getElement().equals("HERE")) {
                        continue;
                    }
                    if (s instanceof Context && entry.getElement().equals("HOLE")) {
                        continue;
                    }
                    kem.registerCompilerWarning(ExceptionType.UNUSED_VAR, errors, "Variable '" + entry.getElement() + "' defined but not used. Prefix variable name with underscore if this is intentional.",
                        loc.get(entry.getElement()));
                }
            } else if (entry.getCount() > 1) {
                if ((entry.getElement().startsWith("_") || entry.getElement().startsWith("?_") || entry.getElement().startsWith("!_") || entry.getElement().startsWith("@_")) && !ResolveAnonVar.isAnonVar(KVariable(entry.getElement()))) {
                    errors.add(KEMException.compilerError("Variable '" + entry.getElement() + "' declared as unused, but it is used. Remove underscore from variable name if this is intentional.",
                          loc.get(entry.getElement())));
                }
            }
        }
    }
}
