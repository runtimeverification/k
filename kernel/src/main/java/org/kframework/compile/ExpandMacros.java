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
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.TransformK;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
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

    private final Map<KLabel, List<Rule>> macros;

    public ExpandMacros(Module mod, KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        macros = stream(mod.rules()).filter(r -> r.att().contains("macro")).collect(Collectors.groupingBy(r -> ((KApply)RewriteToTop.toLeft(r.body())).klabel()));
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
                List<Rule> rules = macros.get(k.klabel());
                if (rules == null)
                    return super.apply(k);
                for (Rule r : rules) {
                    if (!r.requires().equals(BooleanUtils.TRUE)) {
                        throw KEMException.compilerError("Cannot compute macros with side conditions.", r);
                    }
                    K left = RewriteToTop.toLeft(r.body());
                    final Map<KVariable, K> subst = new HashMap<>();
                    if (match(subst, left, k, r)) {
                        return apply(new TransformK() {
                            @Override
                            public K apply(KVariable k) {
                                return subst.get(k);
                            }
                        }.apply(RewriteToTop.toRight(r.body())));
                    }
                }
                return super.apply(k);
            }
        }.apply(term);
    }

    private boolean match(Map<KVariable, K> subst, K pattern, K subject, Rule r) {
        if (pattern instanceof KVariable) {
            if (subst.containsKey(pattern)) {
                return subst.get(pattern).equals(subject);
            } else {
                subst.put((KVariable)pattern, subject);
                return true;
            }
        }
        if (pattern instanceof KApply && subject instanceof KApply) {
           KApply p = (KApply)pattern;
           KApply s = (KApply)subject;
           if (p.klabel() instanceof KVariable || s.klabel() instanceof KVariable) {
               throw KEMException.compilerError("Cannot compute macros with klabel variables.", r);
           }
           if (!p.klabel().name().equals(s.klabel().name())) {
               return false;
           }
           if (p.klist().size() != s.klist().size()) {
               return false;
           }
           boolean match = true;
           for (int i = 0; i < p.klist().size(); i++) {
              match = match && match(subst, p.klist().items().get(i), s.klist().items().get(i), r);
           }
           return match;
        }
        if (subject instanceof KToken && pattern instanceof KToken) {
            return subject.equals(pattern);
        }
        if (subject instanceof KVariable) {
            return false;
        }
        if (subject instanceof KToken || pattern instanceof KToken) {
            return false;
        }
        throw KEMException.compilerError("Cannot compute macros with terms that are not KApply or KVariable.", r);
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
