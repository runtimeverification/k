// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;

import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;
import static org.kframework.definition.Constructors.*;

/**
 * Expands all the macros in a particular module. A macro is a rule (without a side condition)
 * which is tagged with the "macro" attribute. This class assumes that all such macros perform no complex
 * matching on the left hand side of the rule, and generates a simple substitution and recursively applies it.
 */
public class ExpandMacros {

    private final KExceptionManager kem;

    private final Map<KLabel, List<Rule>> macros;
    private final Module mod;
    private final boolean cover;
    private final PrintWriter coverage;
    private final FileChannel channel;

    public ExpandMacros(Module mod, KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        this.mod = mod;
        this.cover = kompileOptions.coverage;
        files.resolveKompiled(".").mkdirs();
        macros = stream(mod.rules()).filter(r -> r.att().contains("macro")).sorted(Comparator.comparing(r -> r.att().contains("owise"))).collect(Collectors.groupingBy(r -> ((KApply)RewriteToTop.toLeft(r.body())).klabel()));
        if (cover) {
            try {
                FileOutputStream os = new FileOutputStream(files.resolveKompiled("coverage.txt"), true);
                channel = os.getChannel();
                coverage = new PrintWriter(new BufferedWriter(new OutputStreamWriter(os)));
            } catch (IOException e) {
                throw KEMException.internalError("Could not write list of rules to coverage document.", e);
            }
        } else {
            channel = null;
            coverage = null;
        }
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
        FileLock lock = null;
        if (cover) {
            try {
                lock = channel.lock();
            } catch (IOException e) {
                throw KEMException.internalError("Could not lock coverage file", e);
            }
        }
        try {
            K result = new TransformK() {
                @Override
                public K apply(KApply k) {
                    List<Rule> rules = macros.get(k.klabel());
                    if (rules == null)
                        return super.apply(k);
                    K applied = super.apply(k);
                    for (Rule r : rules) {
                        if (!r.requires().equals(BooleanUtils.TRUE)) {
                            throw KEMException.compilerError("Cannot compute macros with side conditions.", r);
                        }
                        K left = RewriteToTop.toLeft(r.body());
                        final Map<KVariable, K> subst = new HashMap<>();
                        if (match(subst, left, applied, r)) {
                            if (cover) {
                                if (!r.att().contains("UNIQUE_ID")) System.out.println(r.toString());
                                coverage.println(r.att().get("UNIQUE_ID"));
                            }
                            return apply(new TransformK() {
                                @Override
                                public K apply(KVariable k) {
                                    return subst.get(k);
                                }
                            }.apply(RewriteToTop.toRight(r.body())));
                        }
                    }
                    return applied;
                }
            }.apply(term);
           return result;
        } finally {
             if (cover) {
                coverage.flush();
                try {
                    lock.close();
                } catch (IOException e) {
                    throw KEMException.internalError("Could not unlock coverage file", e);
                }
            }
        }
    }

    private Set<Sort> sort(K k, Rule r) {
        if (k instanceof KVariable) {
            return Collections.singleton(k.att().get(Sort.class));
        } else if (k instanceof KToken) {
            return Collections.singleton(((KToken)k).sort());
        } else if (k instanceof KApply) {
           KApply kapp = (KApply)k;
           if (kapp.klabel() instanceof KVariable) {
               throw KEMException.compilerError("Cannot compute macros with klabel variables.", r);
           }
           Set<Production> prods = new HashSet<>(mutable(mod.productionsFor().apply(kapp.klabel())));
           prods.removeIf(p -> p.arity() != kapp.items().size());
           for (int i = 0; i < kapp.items().size(); i++) {
              final int idx = i;
              Set<Sort> sorts = sort(kapp.items().get(idx), r);
              prods.removeIf(p -> sorts.stream().noneMatch(s -> mod.subsorts().lessThanEq(s, p.nonterminal(idx).sort())));
           }
           Set<Sort> candidates = prods.stream().map(Production::sort).collect(Collectors.toSet());
           return candidates;
        } else {
            throw KEMException.compilerError("Cannot compute macros with sort check on terms that are not KApply, KToken, or KVariable.", r);
        }
    }

    private boolean match(Map<KVariable, K> subst, K pattern, K subject, Rule r) {
        if (pattern instanceof KVariable) {
            if (subst.containsKey(pattern)) {
                return subst.get(pattern).equals(subject);
            } else {
                if (pattern.att().contains(Sort.class)) {
                    Sort patternSort = pattern.att().get(Sort.class);
                    if (sort(subject, r).stream().anyMatch(s -> mod.subsorts().lessThanEq(s, patternSort))) {
                        subst.put((KVariable)pattern, subject);
                        return true;
                    } else {
                        return false;
                    }
                } else {
                    subst.put((KVariable)pattern, subject);
                    return true;
                }
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
        throw KEMException.compilerError("Cannot compute macros with terms that are not KApply, KToken, or KVariable.", r);
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
