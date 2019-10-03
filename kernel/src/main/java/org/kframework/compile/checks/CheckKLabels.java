// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import com.google.common.collect.ImmutableSet;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static org.kframework.kore.KORE.*;

/**
 * Checks to ensure that KLabels in the definition obey rules relating to their use. First, klabels used in rules must
 * be defined by a production in one of the modules imported by the module the rule is in. Second, any given klabel
 * can only be defined in one module. This ensures that klabels don't mix across modules without strictly enforcing
 * the requirement that all klabels be unique, or that all klabels be qualified by their module name.
 */
public class CheckKLabels {
    private final Set<KEMException> errors;

    public CheckKLabels(Set<KEMException> errors) {
        this.errors = errors;
    }

    private final Map<KLabel, Module> klabels = new HashMap<>();

    public void check(Sentence sentence, Module m) {
        VisitK checkKLabels = new VisitK() {
            @Override
            public void apply(InjectedKLabel k) {
                apply(k.klabel(), k);
                super.apply(k);
            }

            @Override
            public void apply(KApply k) {
                apply(k.klabel(), k);
                super.apply(k);
            }

            private void apply(KLabel klabel, K k) {
                if (klabel instanceof KVariable)
                    return;
                if (!m.definedKLabels().apply(klabel) && !isInternalKLabel(klabel.name(), m)) {
                    errors.add(KEMException.compilerError("Found klabel " + klabel.name() + " not defined in any production.", k));
                }
            }
        };
        if (sentence instanceof Rule) {
            Rule rl = (Rule) sentence;
            checkKLabels.apply(rl.body());
            checkKLabels.apply(rl.requires());
            checkKLabels.apply(rl.ensures());
        } else if (sentence instanceof Context) {
            Context ctx = (Context) sentence;
            checkKLabels.apply(ctx.body());
            checkKLabels.apply(ctx.requires());
        } else if (sentence instanceof Production) {
            Production prod = (Production) sentence;
            if (prod.klabel().isDefined()) {
                KLabel klabel = prod.klabel().get();
                if (klabels.containsKey(klabel) && !m.equals(klabels.get(klabel))) {
                    errors.add(KEMException.compilerError("KLabel " + klabel.name() + " defined in multiple modules: " + klabels.get(klabel).name() + " and " + m.name() + ".", prod));
                }
                klabels.put(klabel, m);
            }
        }
    }

    private static final ImmutableSet<String> internalNames = ImmutableSet.of("#cells", "#dots", "#noDots", "#Or", "#fun2", "#fun3", "#withConfig", "<generatedTop>", "#SemanticCastToBag", "_:=K_", "_:/=K_");

    public static boolean isInternalKLabel(String name, Module m) {
        return m.semanticCasts().apply(name) || internalNames.contains(name)|| m.recordProjections().apply(name) || m.sortPredicates().apply(name) || m.sortProjections().apply(name);
    }
}
