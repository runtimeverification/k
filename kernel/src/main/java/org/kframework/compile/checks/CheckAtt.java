// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Set;


/**
 * Created by dwightguth on 1/25/16.
 */
public class CheckAtt {
    private final scala.collection.Set<KLabel> macros;
    private final Set<KEMException> errors;
    private final KExceptionManager kem;
    private final Module m;
    private final boolean isSymbolicKast;

    public CheckAtt(Set<KEMException> errors, KExceptionManager kem, Module m, boolean isSymbolicKast) {
        this.errors = errors;
        this.kem = kem;
        this.m = m;
        this.isSymbolicKast = isSymbolicKast;
        this.macros = m.macroKLabels();
    }

    public void check(Sentence sentence) {
        if (sentence instanceof Rule) {
            check(((Rule) sentence).att(), sentence);
            check((Rule) sentence);
        } else if (sentence instanceof Production) {
            check((Production) sentence);
        }
    }

    private void check(Production prod) {
        if (!prod.sort().equals(Sorts.KItem())) {
            Att sortAtt =  m.sortAttributesFor().getOrElse(prod.sort().head(), () -> Att.empty());
            if (sortAtt.contains(Att.HOOK()) && !sortAtt.get(Att.HOOK()).equals("ARRAY.Array") && !(sortAtt.get(Att.HOOK()).equals("KVAR.KVar") && isSymbolicKast)) {
                if (!prod.att().contains(Att.FUNCTION()) && !prod.att().contains(Att.BRACKET()) &&
                    !prod.att().contains("token") && !(prod.klabel().isDefined() && macros.contains(prod.klabel().get()))) {
                    if (!(prod.sort().equals(Sorts.K()) && ((prod.klabel().isDefined() && (prod.klabel().get().name().equals("#EmptyK") || prod.klabel().get().name().equals("#KSequence"))) || prod.isSubsort()))) {
                        if (!(sortAtt.contains("cellCollection") && prod.isSubsort())) {
                            errors.add(KEMException.compilerError("Cannot add new constructors to hooked sort " + prod.sort(), prod));
                        }
                    }
                }
            }
        }
        if (prod.att().contains("binder") && !isSymbolicKast) {
            if (!prod.att().get("binder").equals("")) {
                errors.add(KEMException.compilerError("Attribute value for 'binder' attribute is not supported.", prod));
            }
            if (prod.nonterminals().size() < 2) {
                errors.add(KEMException.compilerError("Binder productions must have at least two nonterminals.", prod));
            } else if (!m.sortAttributesFor().get(prod.nonterminals().apply(0).sort().head()).getOrElse(() -> Att.empty()).getOptional(Att.HOOK()).orElse("").equals("KVAR.KVar")) {
                errors.add(KEMException.compilerError("First child of binder must have a sort with the 'KVAR.KVar' hook attribute.", prod));
            }
        }
    }

    private void check(Rule rule) {
        if (rule.isMacro()) {
            kem.registerCompilerWarning(ExceptionType.RULE_HAS_MACRO_ATT, errors,
                    "The attribute [" + rule.att().getMacro().get() + "] has been deprecated on rules. Use this label on syntax declarations instead.", rule);
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
