// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.compile.checks.CheckFunctions;
import org.kframework.compile.checks.CheckSmtLemmas;
import org.kframework.definition.Claim;
import org.kframework.definition.Context;
import org.kframework.definition.HasAtt;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.RuleOrClaim;
import org.kframework.definition.Sentence;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Option;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;

import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;

import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
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

    private final Map<KLabel, List<Rule>> macros;
    private final Map<Sort, List<Rule>> macrosBySort;
    private final Module mod;
    private final boolean cover;
    private final PrintWriter coverage;
    private final FileChannel channel;
    private final boolean reverse;
    private final ResolveFunctionWithConfig transformer;
    private final KompileOptions kompileOptions;
    private final KExceptionManager kem;

    public static ExpandMacros fromMainModule(Module mod, FileUtil files, KExceptionManager kem, KompileOptions kompileOptions, boolean reverse) {
        return new ExpandMacros(mod, files, kem, kompileOptions, reverse, true);
    }

    public static ExpandMacros forNonSentences(Module mod, FileUtil files, KompileOptions kompileOptions, boolean reverse) {
        return new ExpandMacros(mod, files, null, kompileOptions, reverse, false);
    }

    private ExpandMacros(Module mod, FileUtil files, KExceptionManager kem, KompileOptions kompileOptions, boolean reverse, boolean sentences) {
        this(sentences ? new ResolveFunctionWithConfig(mod) : null, mod, files, kem, kompileOptions, reverse);
    }

    public ExpandMacros(ResolveFunctionWithConfig transformer, Module mod, FileUtil files, KExceptionManager kem, KompileOptions kompileOptions, boolean reverse) {
        this.mod = mod;
        this.reverse = reverse;
        this.cover = kompileOptions.coverage;
        this.kompileOptions = kompileOptions;
        this.kem = kem;
        files.resolveKompiled(".").mkdirs();
        List<Rule> allMacros = stream(mod.rules()).filter(r -> isMacro(r.att(), reverse)).sorted(Comparator.comparingInt(r -> ModuleToKORE.getPriority(r.att()))).collect(Collectors.toList());
        macros = allMacros.stream().filter(r -> getLeft(r, reverse) instanceof KApply).collect(Collectors.groupingBy(r -> ((KApply)getLeft(r, reverse)).klabel()));
        macrosBySort = stream(mod.allSorts()).collect(Collectors.toMap(s -> s, s -> allMacros.stream().filter(r -> {
          K left = getLeft(r, reverse);
          if (left instanceof KToken || left instanceof KVariable) {
            return sort(left, r).contains(s);
          } else {
            return false;
          }
        }).collect(Collectors.toList())));
        this.transformer = transformer;
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

    private K getLeft(Rule r, boolean reverse) {
        if (reverse) {
            return RewriteToTop.toRight(r.body());
        }
        return RewriteToTop.toLeft(r.body());
    }

    private boolean isMacro(Att att, boolean reverse) {
        return att.contains(Att.ALIAS_REC()) || att.contains(Att.ALIAS()) || (!reverse && (att.contains(Att.MACRO()) || att.contains(Att.MACRO_REC())));
    }

    private Set<KVariable> vars = new HashSet<>();

    void resetVars() {
        vars.clear();
    }

    void gatherVars(K term) {
        new VisitK() {
            @Override
            public void apply(KVariable v) {
                vars.add(v);
                super.apply(v);
            }
        }.apply(term);
    }

    private int counter = 0;
    KVariable newDotVariable(Att att) {
        KVariable newLabel;
        do {
            newLabel = KVariable("_Gen" + (counter++), att.add(Att.ANONYMOUS()));
        } while (vars.contains(newLabel));
        vars.add(newLabel);
        return newLabel;
    }

    private RuleOrClaim expand(RuleOrClaim rule) {
        resetVars();
        gatherVars(rule.body());
        gatherVars(rule.requires());
        gatherVars(rule.ensures());
        RuleOrClaim result = rule.newInstance(expand(rule.body()),
                expand(rule.requires()),
                expand(rule.ensures()),
                rule.att());
        return (RuleOrClaim) check(result);
    }

    private Context expand(Context context) {
        resetVars();
        gatherVars(context.body());
        gatherVars(context.requires());
        Context result = Context(
                expand(context.body()),
                expand(context.requires()),
                context.att());
        return (Context)check(result);
    }

    private Sentence check(Sentence s) {
        Set<KEMException> errors = new HashSet<>();
        new CheckFunctions(errors, mod).check(s);
        new CheckSmtLemmas(errors, mod).check(s);

        /**
         * At this point, all macros inside rules should have been expanded. However, a user could have accidentally
         * left out a rule that expands the macro or incorrectly programmed this rule. If this is the case, rules may
         * contain macros that have not been expanded.
         */
        if (s instanceof RuleOrClaim){
            new VisitK() {
                @Override
                public void apply(KApply k) {
                    Option<Att> atts = mod.attributesFor().get(k.klabel());
                    if (atts.isDefined() && mod.attributesFor().apply(k.klabel()).getMacro().isDefined()) {
                        errors.add(KEMException.compilerError("Rule contains macro symbol that was not expanded", s));
                    }
                    k.klist().items().stream().forEach(i -> super.apply(i));
                }
            }.accept(((RuleOrClaim) s).body());
        }

        if (!errors.isEmpty()) {
          kem.addAllKException(errors.stream().map(e -> e.exception).collect(Collectors.toList()));
          throw KEMException.compilerError("Had " + errors.size() + " structural errors after macro expansion.");
        }
        return s;
    }

    public K expand(K term) {
        if (macros.size() == 0 && macrosBySort.size() == 0)
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
                private Set<Rule> appliedRules = new HashSet<>();

                @Override
                public K apply(KApply k) {
                    List<Rule> rules = macros.get(k.klabel());
                    return applyMacros(k, rules, super::apply);
                }

                private <T extends K> K applyMacros(T k, List<Rule> rules, Function<T, K> superApply) {
                    if (rules == null)
                        return superApply.apply(k);
                    K applied = superApply.apply(k);
                    for (Rule r : rules) {
                        if (!r.requires().equals(BooleanUtils.TRUE)) {
                            throw KEMException.compilerError("Cannot compute macros with side conditions.", r);
                        }
                        K left = RewriteToTop.toLeft(r.body());
                        K right = RewriteToTop.toRight(r.body());
                        if (reverse) {
                            K tmp = left;
                            left = right;
                            right = tmp;
                        }
                        final Map<KVariable, K> subst = new HashMap<>();
                        if (match(subst, left, applied, r) && (r.att().contains(Att.MACRO_REC()) || r.att().contains(Att.ALIAS_REC()) || !appliedRules.contains(r))) {
                            if (cover) {
                                if (!r.att().contains(Att.UNIQUE_ID())) System.out.println(r.toString());
                                coverage.println(r.att().get(Att.UNIQUE_ID()));
                            }
                            Set<Rule> oldAppliedRules = appliedRules;
                            appliedRules = new HashSet<>(appliedRules);
                            appliedRules.add(r);
                            K result = apply(new TransformK() {
                                @Override
                                public K apply(KVariable k) {
                                    K result = subst.get(k);
                                    if (result == null) {
                                      if (k.name().equals("#Configuration")) {
                                        return k;
                                      }
                                      result = newDotVariable(k.att());
                                      subst.put(k, result);
                                    }
                                    return result;
                                }
                            }.apply(right));
                            appliedRules = oldAppliedRules;
                            return result;
                        }
                    }
                    return applied;
                }

                @Override
                public K apply(KToken k) {
                    List<Rule> rules = macrosBySort.get(k.sort());
                    return applyMacros(k, rules, super::apply);
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

    private boolean hasPolyAtt(Production prod, int idx) {
      if (prod.params().isEmpty()) {
        return false;
      }
      for (Sort param : iterable(prod.params())) {
        if (prod.sort().equals(param) && prod.nonterminals().apply(idx).sort().equals(param)) {
          return true;
        }
      }
      return false;
    }


    private Set<Sort> sort(K k, RuleOrClaim r) {
        if (k instanceof KVariable) {
            return Collections.singleton(k.att().getOptional(Sort.class).orElse(null));
        } else if (k instanceof KToken) {
            return Collections.singleton(((KToken)k).sort());
        } else if (k instanceof KApply) {
           KApply kapp = (KApply)k;
           if (kapp.klabel() instanceof KVariable) {
               throw KEMException.compilerError("Cannot compute macros with klabel variables.", r);
           }
           Set<Production> prods = new HashSet<>(mutable(mod.productionsFor().apply(kapp.klabel())));
           prods.removeIf(p -> p.arity() != kapp.items().size());
           Set<Sort> polySorts = new HashSet<>();
           for (int i = 0; i < kapp.items().size(); i++) {
              final int idx = i;
              Set<Sort> sorts = sort(kapp.items().get(idx), r);
              if (prods.stream().anyMatch(p -> hasPolyAtt(p, idx))) {
                  polySorts.addAll(sorts);
              }
              if (!sorts.contains(null)) {
                  prods.removeIf(p -> !hasPolyAtt(p, idx) && sorts.stream().noneMatch(s -> mod.subsorts().lessThanEq(s, p.nonterminal(idx).sort())));
              }
           }
           Set<Sort> candidates = prods.stream().map(Production::sort).collect(Collectors.toSet());
           candidates.addAll(polySorts);
           return candidates;
        } else if (k instanceof KSequence) {
            return Collections.singleton(Sorts.K());
        } else if (k instanceof KAs) {
            return sort(((KAs)k).pattern(), r);
        } else {
            throw KEMException.compilerError("Cannot compute macros with sort check on terms that are not KApply, KToken, or KVariable.", r);
        }
    }

    private boolean match(Map<KVariable, K> subst, K pattern, K subject, RuleOrClaim r) {
        if (pattern instanceof KVariable) {
            if (subst.containsKey(pattern)) {
                return subst.get(pattern).equals(subject);
            } else {
                if (pattern.att().contains(Sort.class)) {
                    Sort patternSort = pattern.att().get(Sort.class);
                    if (sort(subject, r).stream().anyMatch(s -> s == null || mod.subsorts().lessThanEq(s, patternSort))) {
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
             if (!mod.overloads().greaterThan(mod.productionsFor().apply(p.klabel()).head(), mod.productionsFor().apply(s.klabel()).head())) {
               return false;
             }
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

    public static boolean isMacro(HasAtt s) {
        return s.isMacro();
    }

    public Sentence expand(Sentence s) {
        if (s instanceof Rule && !isMacro(s)) {
            return transformer.resolve(expand((Rule) s), mod);
        } else if (s instanceof Claim) {
            return transformer.resolve(expand((Claim) s), mod);
        } else if (s instanceof Context) {
            return transformer.resolve(expand((Context) s), mod);
        } else {
            return s;
        }
    }
}
