// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

/**
 * Created by dwightguth on 1/25/16.
 */
public class CheckAtt {
    private final Set<KEMException> errors;
    private final Module m;

    public CheckAtt(Set<KEMException> errors, Module m) {
        this.errors = errors;
        this.m = m;
    }

    public void check(Sentence sentence) {
        if (sentence instanceof Rule) {
            check(((Rule) sentence).att(), sentence);
        } else if (sentence instanceof Production) {
            check((Production) sentence);
        }
    }

    private void check(Production prod) {
        if (!prod.sort().equals(Sorts.KItem())) {
            Att sortAtt =  m.sortAttributesFor().getOrElse(prod.sort().head(), () -> Att.empty());
            if (sortAtt.contains(Att.HOOK()) && !sortAtt.get(Att.HOOK()).equals("ARRAY.Array")) {
                if (!prod.att().contains(Att.FUNCTION()) && !prod.att().contains("token")) {
                    if (!(prod.sort().equals(Sorts.K()) && ((prod.klabel().isDefined() && (prod.klabel().get().name().equals("#EmptyK") || prod.klabel().get().name().equals("#KSequence"))) || prod.isSubsort()))) {
                        if (!(sortAtt.contains("cellCollection") && prod.isSubsort())) {
                            errors.add(KEMException.compilerError("Cannot add new constructors to hooked sort " + prod.sort(), prod));
                        }
                    }
                }
            }
        }
    }

    private void check(Att att, HasLocation loc) {
        if (att.contains(Att.OWISE()) && att.contains(Att.SIMPLIFICATION())) {
          errors.add(KEMException.compilerError("owise attribute is not supported on simplification rules.", loc));
        }
        if (att.contains(Att.PRIORITY()) && att.contains(Att.SIMPLIFICATION())) {
          errors.add(KEMException.compilerError("priority attribute is not supported on simplification rules.", loc));
        }
    }
}
