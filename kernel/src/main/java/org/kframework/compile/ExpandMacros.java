// Copyright (c) 2015-2016 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

/**
 * Expands all the macros in a particular module. A macro is a rule (without a side condition)
 * which is tagged with the "macro" attribute. This class assumes that all such macros perform no complex
 * matching on the left hand side of the rule, and generates a simple substitution and recursively applies it.
 */
public class ExpandMacros {

    private final KExceptionManager kem;

    private final Map<KLabel, Rule> macros;

    public ExpandMacros(Module mod, KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        macros = stream(mod.rules()).filter(r -> r.att().contains("macro")).collect(Collectors.toMap(r -> ((KApply)RewriteToTop.toLeft(r.body())).klabel(), Function.identity()));
    }

    private Rule expand(Rule rule) {
        return Rule(expand(rule.body()),
                expand(rule.requires()),
                expand(rule.ensures()),
                rule.att());
    }

    private Context expand(Context context) {
        return Context(
                expand(context.body()),
                expand(context.requires()),
                context.att());
    }

    public K expand(K term) {
        if (macros.size() == 0)
            return term;
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                Rule r = macros.get(k.klabel());
                if (r == null)
                    return super.apply(k);
                if (!r.requires().equals(BooleanUtils.TRUE)) {
                    throw KEMException.compilerError("Cannot compute macros with side conditions.", r);
                }
                K left = RewriteToTop.toLeft(r.body());
                KList list;
                if (left instanceof KApply) {
                    list = ((KApply) left).klist();
                } else {
                    throw KEMException.compilerError("Cannot compute macros that are not function-like.", r);
                }
                final Map<KVariable, K> subst = new HashMap<>();
                for (int i = 0; i < k.items().size(); i++) {
                    K param = list.items().get(i);
                    if (!(param instanceof KVariable)) {
                        throw KEMException.compilerError("Cannot compute macros that are not function-like.", r);
                    }
                    if (subst.containsKey(param)) {
                        throw KEMException.compilerError("Cannot compute macros with non-linear variables.", r);
                    }
                    subst.put(((KVariable)param), apply(k.items().get(i)));
                }
                return apply(new TransformK() {
                    @Override
                    public K apply(KVariable k) {
                        return subst.get(k);
                    }
                }.apply(RewriteToTop.toRight(r.body())));
            }
        }.apply(term);
    }

    public Sentence expand(Sentence s) {
        if (s instanceof Rule && !s.att().contains("macro")) {
            return expand((Rule) s);
        } else if (s instanceof Context) {
            return expand((Context) s);
        } else {
            return s;
        }
    }

}
