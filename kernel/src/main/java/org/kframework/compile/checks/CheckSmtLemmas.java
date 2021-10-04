package org.kframework.compile.checks;

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
        if ((sentence instanceof Rule) && sentence.att().contains("smt-lemma")) {
            check((Rule) sentence);
        }
    }

    private void check(Rule rule){
        if (!(rule.body() instanceof KRewrite)) {
            return;
        }
        new VisitK() {
            @Override
            public void apply(KRewrite k) {
                super.apply(k.left());
                super.apply(k.right());
            }

            @Override
            public void apply(KApply k) {
                if (!k.att().toString().matches(".*smtlib.*|.*smt-hook.*")) {
                    errors.add(KEMException.compilerError(
                            "Invalid smt-lemma term detected. All terms in smt-lemma rules require smt-hook or smtlib labels", k));
                }
                k.klist().items().stream().forEach(ki -> super.apply(ki));
            }
        }.accept(rule.body());
    }
}
