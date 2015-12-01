// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.kframework.Collections;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import scala.collection.Set;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.Att;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Generates sort predicates from the subsort hierarchy of the module. This module assumes that the backend implements
 * the following rules:
 * isSort(#token(Sort, _)) => true
 * isK(K) => true
 * isKItem(K1(K2)) => true
 * isKItem(#token(_, _)) => true
 *
 * plus one sort membership function for each builtin-hooked sort.
 */
public class GenerateSortPredicateRules {

    private final Definition def;
    private Module mod;
    private java.util.Set<Rule> predicateRules;

    public GenerateSortPredicateRules(Definition def) {
        this.def = def;
    }

    public Module gen(Module mod) {
        this.mod = mod;
        predicateRules = stream(mod.rules()).filter(this::isPredicate).collect(Collectors.toSet());
        return Module(mod.name(), mod.imports(), (Set<Sentence>) mod.localSentences().$bar(stream(mod.definedSorts())
                .flatMap(this::gen).collect(Collections.toSet())), mod.att());
    }

    private Stream<? extends Sentence> gen(Sort sort) {
        List<Sentence> res = new ArrayList<>();
        Production prod = Production("is" + sort.name(), Sorts.Bool(),
                Seq(Terminal("is" + sort.name()), Terminal("("), NonTerminal(Sorts.K()), Terminal(")")),
                Att().add(Attribute.FUNCTION_KEY).add(Attribute.PREDICATE_KEY, sort.name()));
        res.add(prod);
        java.util.Set<Sort> nonProtectingSubsorts = new HashSet<>();
        nonProtectingSubsorts.add(sort);
        // we compute the set of subsorts which protect the parent sort (ie do not add terms to it)
        // in order to optimize away some cases from being checked during sort computation at runtime
        stream(mod.definedSorts()).filter(s -> mod.subsorts().lessThanEq(s, sort)).forEach(subsort -> {
            MutableBoolean isProtecting = new MutableBoolean(true);
            stream(mod.definedSorts()).filter(s -> mod.subsorts().lessThanEq(s, subsort)).forEach(candidateSort -> {
                if (predicateRules.stream().filter(r -> isPredicateFor(r, candidateSort)).findAny().isPresent()) {
                    // the subsort has subsorts with predicate rules, so it may have introduced arbitrary terms into the membership
                    isProtecting.setFalse();
                }
                stream(mod.productions()).filter(p -> p.sort().equals(candidateSort) && p.klabel().isDefined()).forEach(candidateProduction -> {
                    // for each production, check if there exists a production in the parent sort which is protected by this production
                    if (!stream(mod.productionsFor().apply(candidateProduction.klabel().get())).filter(p -> p.sort().equals(sort) && p.arity() == candidateProduction.arity()).anyMatch(possibleParentProduction -> {
                        for (int i = 0; i < candidateProduction.arity(); i++) {
                            if (!mod.subsorts().lessThanEq(candidateProduction.nonterminal(i).sort(), possibleParentProduction.nonterminal(i).sort())) {
                                // this production cannot protect the parent because its children are broader than the parent productions
                                return false;
                            }
                        }
                        return true;
                    })) {
                        // if the candidate production is not a special case of a production declared by the parent sort, then
                        // this is a new term added to the membership
                        isProtecting.setFalse();
                    }
                });
            });
            if (!isProtecting.getValue()) {
                nonProtectingSubsorts.add(subsort);
            }
        });
        stream(mod.productions()).filter(p -> mod.subsorts().lessThanEq(p.sort(), sort)).filter(p -> nonProtectingSubsorts.contains(p.sort())).distinct().forEach(p -> {
            if (p.klabel().isDefined() && !p.att().contains(Attribute.FUNCTION_KEY)) {
                List<K> klist = new ArrayList<>();
                List<K> side = new ArrayList<>();
                int i = 0;
                List<NonTerminal> nts = stream(p.items()).filter(pi -> pi instanceof NonTerminal).map(pi -> (NonTerminal) pi).collect(Collectors.toList());
                for (NonTerminal nt : nts) {
                    KVariable v = KVariable("K" + i++, Att().add(Attribute.SORT_KEY, nt.sort().name()));
                    klist.add(v);
                    side.add(KApply(KLabel("is" + nt.sort().name()), v));
                }
                ;
                Optional<K> sideCondition = side.stream().reduce(BooleanUtils::and);
                K requires;
                if (!sideCondition.isPresent()) {
                    requires = BooleanUtils.TRUE;
                } else {
                    requires = sideCondition.get();
                }
                Rule r = Rule(KRewrite(KApply(KLabel("is" + sort.name()), KApply(p.klabel().get(), KList(klist))), BooleanUtils.TRUE), requires, BooleanUtils.TRUE);
                res.add(r);
            }
        });
        stream(mod.definedSorts()).filter(s -> mod.subsorts().lessThanEq(s, sort)).distinct().forEach(s -> {
            res.add(Rule(KRewrite(KApply(KLabel("is" + sort.name()), KApply(KLabel("#KToken"), KToken(s.name(), Sorts.KString()), KVariable("_"))), BooleanUtils.TRUE),
                    BooleanUtils.TRUE,
                    BooleanUtils.TRUE));
            if (nonProtectingSubsorts.contains(s)) {
                res.addAll(predicateRules.stream().filter(r -> isPredicateFor(r, s)).map(r -> promotePredicate(r, sort)).collect(Collectors.toList()));
            }
        });
        res.add(Rule(KRewrite(KApply(KLabel("is" + sort.name()), KVariable("K")), BooleanUtils.FALSE), BooleanUtils.TRUE, BooleanUtils.TRUE, Att().add("owise")));
        return res.stream();
    }

    private boolean isPredicateFor(Rule r, Sort s) {
        Optional<String> sort = getPredicateSort(r);
        return sort.isPresent() && sort.get().equals(s.name());
    }

    private boolean isPredicate(Rule r) {
        return getPredicateSort(r).isPresent();
    }

    private Optional<String> getPredicateSort(Rule r) {
        KLabel topKLabel;
        Optional<String> sort;
        if (r.body() instanceof KApply) {
            topKLabel = ((KApply) r.body()).klabel();
            sort = mod.attributesFor().apply(topKLabel).<String>getOptional(Attribute.PREDICATE_KEY);
        } else if (r.body() instanceof KRewrite) {
            KRewrite rw = (KRewrite) r.body();
            if (rw.left() instanceof KApply) {
                topKLabel = ((KApply) rw.left()).klabel();
                sort = mod.attributesFor().apply(topKLabel).<String>getOptional(Attribute.PREDICATE_KEY);
            } else {
                sort = Optional.empty();
            }
        } else
            sort = Optional.empty();
        return sort;
    }

    /**
     * Takes a rule representing a predicate of one sort and promotes it to a rule representing a predicate for one of its supersorts
     */
    private Rule promotePredicate(Rule r, Sort s) {
        K left = RewriteToTop.toLeft(r.body());
        K right = RewriteToTop.toRight(r.body());
        if (left instanceof KApply) {
            // the case where a rewrite applies unconditionally may be dependent on the klabel, so we hoist the rhs into the side condition
            return Rule(KRewrite(KApply(KLabel("is" + s.name()), ((KApply) left).klist()), BooleanUtils.TRUE), BooleanUtils.and(r.requires(), right), r.ensures(), r.att());
        } else {
            throw new IllegalArgumentException("not a predicate rule");
        }
    }
}
