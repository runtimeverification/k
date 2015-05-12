package org.kframework.kore.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

public class ResolveHeatCoolAttribute {

    private Rule resolve(Rule rule) {
        return Rule(
                rule.body(),
                transform(rule.requires(), rule.att()),
                rule.ensures(),
                rule.att());
    }

    private Context resolve(Context context) {
        return new Context(
                context.body(),
                transform(context.requires(), context.att()),
                context.att());
    }

    private K transform(K requires, Att att) {
        String sort = att.<String>getOptional("result").orElse("KResult");
        K predicate = KApply(KLabel("is" + sort), KVariable("HOLE"));
        if (att.contains("heat")) {
            return BooleanUtils.and(requires, BooleanUtils.not(predicate));
        } else if (att.contains("cool")) {
            return BooleanUtils.and(requires, predicate);
        }
        throw new AssertionError("unreachable");
    }

    public synchronized Sentence resolve(Sentence s) {
        if (!s.att().contains("heat") && !s.att().contains("cool")) {
            return s;
        }
        if (s instanceof Rule) {
            return resolve((Rule) s);
        } else if (s instanceof Context) {
            return resolve((Context) s);
        } else {
            return s;
        }
    }
}
