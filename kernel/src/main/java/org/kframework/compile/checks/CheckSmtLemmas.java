package org.kframework.compile.checks;

import org.kframework.attributes.Att;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KApply;
import org.kframework.kore.KRewrite;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;

public class CheckSmtLemmas {
    private final Set<KEMException> errors;
    private final Module m;

    public CheckSmtLemmas(Set<KEMException> errors, Module m) {
        this.errors = errors;
        this.m = m;
    }

    public void check(Sentence sentence) {
        if ((sentence instanceof Rule) && sentence.att().contains(Att.SMT_LEMMA())) {
            check((Rule) sentence);
        }
    }

    private void check(Rule rule){
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (m.productionsFor().isDefinedAt(k.klabel()) && !m.productionsFor().get(k.klabel()).get()
                        .exists(p -> p.att().contains(Att.SMT_HOOK()) || p.att().contains(Att.SMTLIB()))) {
                    errors.add(KEMException.compilerError(
                            "Invalid term in smt-lemma detected. All terms in smt-lemma rules require smt-hook or smtlib labels", k));
                }

                k.klist().items().stream().forEach(ki -> super.apply(ki));
            }
        }.accept(rule.body());
    }
}
