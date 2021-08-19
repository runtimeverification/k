// Copyright (c) 2017-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kompile.Kompile;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.compile.checks.ComputeUnboundVariables;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Resolves #fun KApplies.
 *
 * The rule Ctx[#fun(Pattern)(Expression)] is equivalent to the following sentences assuming some completely unique KLabel #lambda1 not used in any token:
 *
 * rule Ctx[#lambda1(Expression)]
 * syntax K ::= #lambda1(K) [function]
 * rule #lambda1(LHS) => RHS
 *
 * Where LHS is the LHS of Pattern and RHS is the RHS of Pattern.
 *
 * Note that if a variable is used in the rhs of the fun expression which is not bound in its lhs, it is added as a
 * closure parameter to the generated function.
 *
 * We purposely resolve this construct as early as possible in the pipeline so that later stages which insert implicit
 * side conditions into the rule insert them into the correct rule.
 */
public class ResolveFun {

    public ResolveFun(boolean kore) {
      this.kore = kore;
    }

    private final boolean kore;
    private final Set<Production> funProds = new HashSet<>();
    private final Set<Rule> funRules = new HashSet<>();
    private Module module;
    private final Set<KLabel> klabels = new HashSet<>();

    private KLabel getUniqueLambdaLabel(String nameHint1, String nameHint2) {
        if (klabels.isEmpty()) {
            klabels.addAll(mutable(module.definedKLabels()));
        }
        int counter = 0;
        KLabel freezer;
        do {
            freezer = KLabel("#lambda" + nameHint1 + "_" + nameHint2 + "_" + (counter++ == 0 ? "" : counter));
        } while (klabels.contains(freezer));
        klabels.add(freezer);
        return freezer;
    }

    private Rule resolve(Rule rule) {
        return new Rule(
                transform(rule.body()),
                transform(rule.requires()),
                transform(rule.ensures()),
                rule.att());
    }

    private K transform(K body) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                KLabel lbl = k.klabel();
                if (!(lbl instanceof KVariable) && lbl.name().equals("#fun2") || lbl.name().equals("#fun3") || lbl.name().equals("#let") || lbl.equals(KLabels.IN_K) || lbl.equals(KLabels.NOT_IN_K)) {
                    String nameHint1 = "", nameHint2 = "";
                    K arg, body;
                    if (lbl.name().equals("#fun3")) {
                        body = KRewrite(k.items().get(0), k.items().get(1));
                        arg = k.items().get(2);
                    } else if (lbl.name().equals("#let")) {
                        body = KRewrite(k.items().get(0), k.items().get(2));
                        arg = k.items().get(1);
                    } else {
                        body = k.items().get(0);
                        arg = k.items().get(1);
                    }
                    if (arg instanceof KVariable) {
                        nameHint1 = ((KVariable) arg).name();
                    } else if (arg instanceof KApply
                            && ((KApply) arg).klabel().name().startsWith("#SemanticCastTo")
                            && ((KApply) arg).items().get(0) instanceof KVariable) {
                        nameHint1 = ((KVariable) ((KApply) arg).items().get(0)).name();
                    }
                    if (body instanceof KApply) {
                        nameHint2 = ((KApply) body).klabel().name();
                    }
                    KLabel fun = getUniqueLambdaLabel(nameHint1, nameHint2);
                    Sort lhsSort = sort(RewriteToTop.toLeft(body));
                    Sort argSort = sort(arg);
                    Sort lubSort = AddSortInjections.lubSort(lhsSort, argSort, null, body, module);
                    if (lbl.name().equals("#fun3") || lbl.name().equals("#fun2") || lbl.name().equals("#let")) {
                        funProds.add(funProd(fun, body, lubSort));
                        funRules.add(funRule(fun, body, k.att()));
                    } else {
                        funProds.add(predProd(fun, body, lubSort));
                        funRules.add(predRule(fun, body, k.att()));
                        funRules.add(owiseRule(fun, body, lubSort, k.att()));
                    }
                    List<K> klist = new ArrayList<>();
                    klist.add(apply(arg));
                    klist.addAll(closure(body));
                    K funCall = KApply(fun, KList(klist));
                    if (lbl.equals(KLabels.NOT_IN_K)) {
                      return BooleanUtils.not(funCall);
                    }
                    return funCall;
                }
                return super.apply(k);
            }
        }.apply(body);
    }

    private Rule funRule(KLabel fun, K k, Att att) {
        return lambdaRule(fun, k, k, att, RewriteToTop::toRight);
    }

    private Rule predRule(KLabel fun, K k, Att att) {
        return lambdaRule(fun, k, k, att, x -> BooleanUtils.TRUE);
    }

    private Rule owiseRule(KLabel fun, K k, Sort arg, Att att) {
        return lambdaRule(fun, KApply(KLabel("#SemanticCastTo" + arg.toString()), KVariable("#Owise")), k, att.add(Att.OWISE()), x -> BooleanUtils.FALSE);
    }

    private Rule lambdaRule(KLabel fun, K body, K closure, Att att, UnaryOperator<K> getRHS) {
        K resolved = transform(body);
        K withAnonVars = new ResolveAnonVar().resolveK(resolved);
        List<K> klist = new ArrayList<>();
        klist.add(RewriteToTop.toLeft(withAnonVars));
        klist.addAll(closure(closure));
        K rewrite = KRewrite(KApply(fun, KList(klist)), getRHS.apply(withAnonVars));
        K renamed = new TransformK() {
            public K apply(KVariable k) {
              if (k.name().startsWith("!")) {
                return KVariable("#_" + k.name().substring(1), k.att());
              }
              return k;
            }
        }.apply(rewrite);
        return Rule(renamed,
                BooleanUtils.TRUE, BooleanUtils.TRUE, att);
    }

    private List<KVariable> closure(K k) {
        Set<KEMException> errors = new HashSet<>();
        Set<KVariable> vars = new HashSet<>();
        List<KVariable> result = new ArrayList<>();
        new GatherVarsVisitor(true, errors, vars, false).apply(k);
        new ComputeUnboundVariables(true, true, errors, vars, result::add).apply(k);
        return result;
    }

    private Production funProd(KLabel fun, K k, Sort arg) {
        return lambdaProd(fun, k, arg, sort(RewriteToTop.toRight(k)));
    }

    private Production predProd(KLabel fun, K k, Sort arg) {
        return lambdaProd(fun, k, arg, Sorts.Bool());
    }

    private Production lambdaProd(KLabel fun, K k, Sort arg, Sort rhs) {
        List<ProductionItem> pis = new ArrayList<>();
        pis.add(Terminal(fun.name()));
        pis.add(Terminal("("));
        pis.add(NonTerminal(arg));
        for (KVariable var : closure(k)) {
            pis.add(Terminal(","));
            pis.add(NonTerminal(var.att().getOptional(Sort.class).orElse(Sorts.K())));
        }
        pis.add(Terminal(")"));
        return Production(fun, rhs,
                immutable(pis),
                Att().add("function"));
    }

    private Sort sort(K k) {
        if (k instanceof KSequence)
            return Sorts.K();
        if (k instanceof KAs)
            return sort(((KAs) k).pattern());
        if (k instanceof InjectedKLabel)
            return Sorts.KItem();
        if (k instanceof KToken)
            return ((KToken) k).sort();
        if (k instanceof KApply) {
            if (kore) {
                AddSortInjections inj = new AddSortInjections(module);
                return inj.sort(k, Sorts.K());
            } else {
                return k.att().get(Production.class).sort();
            }
        }
        if (k instanceof KVariable)
            return Sorts.K();
        throw KEMException.compilerError("Could not compute sort of term", k);
    }

    private Context resolve(Context context) {
        return new Context(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    private ContextAlias resolve(ContextAlias context) {
        return new ContextAlias(
                transform(context.body()),
                transform(context.requires()),
                context.att());
    }

    public Sentence resolve(Sentence s) {
        if (s instanceof Rule) {
            return resolve((Rule) s);
        } else if (s instanceof Context) {
            return resolve((Context) s);
        } else if (s instanceof ContextAlias) {
            return resolve((ContextAlias) s);
        } else {
            return s;
        }
    }

    public Module resolve(Module m) {
        module = Kompile.subsortKItem(m);
        funProds.clear();
        funRules.clear();
        Set<Sentence> newSentences = stream(m.localSentences()).map(this::resolve).collect(Collectors.toSet());
        newSentences.addAll(funProds);
        newSentences.addAll(funRules);
        return Module(m.name(), m.imports(), immutable(newSentences), m.att());
    }
}
