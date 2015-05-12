package org.kframework.kore.compile;

import org.kframework.definition.Context;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KSequence;

import java.util.ArrayList;
import java.util.List;

import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Raises all rules into a form with a KSequence in every position that expects a term of sort K.
 */
public class LiftToKSequence {


    public synchronized Sentence convert(Sentence s) {
        if (s instanceof Rule) {
            return convert((Rule) s);
        } else if (s instanceof Context) {
            return convert((Context) s);
        } else {
            return s;
        }
    }

    private Rule convert(Rule rule) {
        return Rule(
                convert(rule.body()),
                convert(rule.requires()),
                convert(rule.ensures()),
                rule.att());
    }

    private Context convert(Context context) {
        return Context(
                convert(context.body()),
                convert(context.requires()),
                context.att());
    }

    public K convert(K term) {
        K result = new TransformKORE()  {
            @Override
            public K apply(KApply k) {
                List<K> children = new ArrayList<>();
                for (K child : k.klist().items()) {
                    K res = apply(child);
                    if (res instanceof KSequence) {
                        children.add(res);
                    } else {
                        children.add(KSequence(res));
                    }
                }
                return KApply(k.klabel(), KList(children), k.att());
            }
        }.apply(term);
        if (result instanceof KSequence) {
            return result;
        } else {
            return KSequence(result);
        }
    }
}
