// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kore.FoldK;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import scala.Tuple2;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

public class AddSortInjections {

    private final Module mod;
    private final Map<KLabel, KLabel> collectionFor;

    private int freshSortParamCounter = 0;
    private Set<String> sortParams = new HashSet<>();
    public static final String SORTPARAM_NAME = "#SortParam";

    public AddSortInjections(Module mod) {
        this.mod = mod;
        this.collectionFor = ConvertDataStructureToLookup.collectionFor(mod);
    }

    public Sentence addInjections(Sentence s) {
        if (s instanceof Rule) {
            return addInjections((Rule) s);
        } else if (s instanceof Context) {
            return addInjections((Context) s);
        } else {
            return s;
        }
    }

    public Rule addInjections(Rule rule) {
        initSortParams();
        K body = addTopSortInjections(rule.body());
        K requires = internalAddSortInjections(rule.requires(), Sorts.Bool());
        K ensures = internalAddSortInjections(rule.ensures(), Sorts.Bool());
        Att att = rule.att();
        if (!sortParams.isEmpty()) {
            att = att.add("sortParams", Set.class, new HashSet<>(sortParams));
        }
        return new Rule(body, requires, ensures, att);
    }

    public K addInjections(K term) {
        Sort topSort = sort(term, Sorts.K());
        K result = addSortInjections(term, topSort);
        return result;
    }

    public K addSortInjections(K term, Sort topSort) {
        initSortParams();
        return internalAddSortInjections(term, topSort);
    }

    private boolean collectionIsMap(KLabel collectionLabel) {
        return mod.attributesFor().apply(collectionLabel).contains(Attribute.COMMUTATIVE_KEY)
                && !mod.attributesFor().apply(collectionLabel).contains(Attribute.IDEMPOTENT_KEY)
                && !mod.attributesFor().apply(collectionLabel).contains(Att.bag());
    }

    private K addTopSortInjections(K body) {
        if (new FoldK<Boolean>() {
            @Override
            public Boolean unit() {
                return false;
            }

            @Override
            public Boolean apply(KRewrite k) {
                return true;
            }

            @Override
            public Boolean merge(Boolean a, Boolean b) {
                return a || b;
            }
        }.apply(body)) {
            body = KRewrite(RewriteToTop.toLeft(body), RewriteToTop.toRight(body));
        }
        Sort sort = sort(body, null);
        if (sort == null) sort = freshSortParam();
        return internalAddSortInjections(body, sort);
    }

    private K internalAddSortInjections(K term, Sort expectedSort) {
        Sort actualSort = sort(term, expectedSort);
        if (actualSort == null) {
            actualSort = expectedSort;
        }
        if (actualSort.equals(expectedSort)) {
            return visitChildren(term, actualSort);
        } else if (expectedSort.equals(Sorts.K())) {
            if (actualSort.equals(Sorts.KItem())) {
                return KSequence(visitChildren(term, actualSort));
            } else {
                return KSequence(KApply(KLabel("inj", actualSort, Sorts.KItem()), KList(visitChildren(term, actualSort)), Att.empty().add(Sort.class, Sorts.KItem())));
            }
        } else {
            String hookAtt = mod.sortAttributesFor().get(expectedSort).getOrElse(() -> Att()).getOptional("hook").orElse("");
            if ((hookAtt.equals("MAP.Map") || hookAtt.equals("SET.Set") || hookAtt.equals("LIST.List")) && term instanceof KApply) {
                for (KLabel collectionLabel : collectionFor.keySet()) {
                    Optional<String> wrapElement = mod.attributesFor().apply(collectionLabel).getOptional("wrapElement");
                    if (wrapElement.isPresent()) {
                        KLabel wrappedLabel = KLabel(wrapElement.get());
                        KLabel elementLabel = KLabel(mod.attributesFor().apply(collectionLabel).get("element"));
                        KApply k = (KApply)term;
                        if (k.klabel().equals(wrappedLabel)) {
                            if (collectionIsMap(collectionLabel)) {
                                // Map
                                return KApply(elementLabel, KList(k.klist().items().get(0), visitChildren(k, actualSort)), Att.empty().add(Sort.class, expectedSort));
                            } else {
                                return KApply(elementLabel, KList(visitChildren(k, actualSort)), Att.empty().add(Sort.class, expectedSort));
                            }
                        }
                    }
                }
            }
            return KApply(KLabel("inj", actualSort, expectedSort), KList(visitChildren(term, actualSort)), Att.empty().add(Sort.class, expectedSort));
        }
    }

    private Context addInjections(Context context) {
        return new Context(internalAddSortInjections(context.body(), Sorts.K()), internalAddSortInjections(context.requires(), Sorts.Bool()), context.att());
    }

    private void initSortParams() {
        freshSortParamCounter = 0;
        sortParams.clear();
    }

    private K visitChildren(K term, Sort actualSort) {
        Att att = term.att().add(Sort.class, actualSort);
        if (actualSort.name().equals(SORTPARAM_NAME)) {
            sortParams.add(actualSort.params().head().name());
        }
        if (term instanceof KApply) {
            KApply kapp = (KApply)term;
            if (kapp.klabel().name().equals("inj")) {
                return term;
            }
            Production prod = production(kapp);
            List<K> children = new ArrayList<>();
            Map<Integer,Sort> expectedSorts = new HashMap<>();
            List<Sort> args = new ArrayList<>();
            if (prod.params().nonEmpty()) {
                for (Sort param : iterable(prod.params())) {
                    Sort expectedSort;
                    Set<Integer> positions = getPositions(param, prod);
                    if (prod.sort().equals(param)) {
                        expectedSort = actualSort;
                    } else {
                        final Sort freshSortParam = freshSortParam();
                        List<Sort> polySorts = positions.stream()
                                .map(p -> sort(kapp.items().get(p), freshSortParam))
                                .collect(Collectors.toList());
                        expectedSort = lub(polySorts, null, kapp, mod);
                    }
                    args.add(expectedSort);
                    for (Integer p : positions) {
                        expectedSorts.put(p, expectedSort);
                    }
                }
            }
            for (int i = 0; i < kapp.items().size(); i++) {
                Sort expectedSort = expectedSorts.getOrDefault(i, prod.nonterminal(i).sort());
                K child = kapp.items().get(i);
                children.add(internalAddSortInjections(child, expectedSort));
            }
            return KApply(KLabel(kapp.klabel().name(), immutable(args)), KList(children), att);
        } else if (term instanceof KRewrite) {
            KRewrite rew = (KRewrite) term;
            return KRewrite(internalAddSortInjections(rew.left(), actualSort), internalAddSortInjections(rew.right(), actualSort), att);
        } else if (term instanceof KVariable) {
            return KVariable(((KVariable) term).name(), att);
        } else if (term instanceof KToken) {
            return KToken(((KToken) term).s(), ((KToken) term).sort(), att);
        } else if (term instanceof InjectedKLabel) {
            return InjectedKLabel(((InjectedKLabel) term).klabel(), att);
        } else if (term instanceof KSequence) {
            KSequence kseq = (KSequence)term;
            List<K> children = new ArrayList<>();
            for (int i = 0; i < kseq.size(); i++) {
                K child = kseq.items().get(i);
                Sort childSort = sort(child, Sorts.KItem());
                if (childSort.equals(Sorts.K())) {
                    children.add(internalAddSortInjections(child, Sorts.K()));
                } else {
                    children.add(internalAddSortInjections(child, Sorts.KItem()));
                }
            }
            return KSequence(children, att);
        } else if (term instanceof KAs) {
            KAs kas = (KAs)term;
            return KAs(internalAddSortInjections(kas.pattern(), actualSort), kas.alias(), att);
        } else {
            throw KEMException.internalError("Invalid category of k found.", term);
        }
    }

    private Set<Integer> getPositions(Sort param, Production prod) {
        return IntStream.range(0, prod.nonterminals().size())
                        .mapToObj(i -> Tuple2.apply(prod.nonterminals().apply(i), i))
                        .filter(t -> t._1().sort().equals(param))
                        .map(t -> t._2())
                        .collect(Collectors.toSet());
    }

    public Sort sort(K term, Sort expectedSort) {
        if (term instanceof KApply) {
            KApply kapp = (KApply)term;
            if (kapp.klabel().name().equals("inj")) {
                return kapp.klabel().params().apply(1);
            }
            if (kapp.klabel().name().startsWith("#SemanticCastTo")) {
                return Outer.parseSort(kapp.klabel().name().substring("#SemanticCastTo".length()));
            }
            if (kapp.klabel().name().equals("#fun2")) {
                return sort(kapp.items().get(0), expectedSort);
            }
            if (kapp.klabel().name().equals("#fun3")) {
                return sort(kapp.items().get(1), expectedSort);
            }
            if (kapp.klabel().name().equals("_:=K_")) {
                return Sorts.Bool();
            }
            if (kapp.klabel().name().equals("_:/=K_")) {
                return Sorts.Bool();
            }
            Production prod = production(kapp);
            if (prod.params().nonEmpty()) {
                for (Sort param : iterable(prod.params())) {
                    if (prod.sort().equals(param)) {
                        Set<Integer> positions = getPositions(param, prod);
                        Set<Sort> children = new HashSet<>();
                        for (int position : positions) {
                            children.add(sort(kapp.items().get(position), expectedSort));
                        }
                        children.remove(null);
                        if (children.size() == 0) {
                            return expectedSort;
                        }
                        return lub(children, expectedSort, term, mod);
                    }
                }
            }
            return production((KApply)term).sort();
        } else if (term instanceof KRewrite) {
            KRewrite rew = (KRewrite)term;
            Sort leftSort = sort(rew.left(), expectedSort);
            Sort rightSort = sort(rew.right(), expectedSort);
            return lubSort(leftSort, rightSort, expectedSort, term, mod);
       } else if (term instanceof KToken) {
            return ((KToken) term).sort();
        } else if (term instanceof KVariable) {
            return term.att().getOptional(Sort.class).orElse(Sorts.K());
        } else if (term instanceof KSequence) {
            return Sorts.K();
        } else if (term instanceof InjectedKLabel) {
            return Sorts.KItem();
        } else if (term instanceof KAs) {
            KAs as = (KAs) term;
            Sort patternSort = sort(as.pattern(), expectedSort);
            Sort rightSort = sort(as.alias(), expectedSort);
            return lubSort(patternSort, rightSort, expectedSort, term, mod);
        } else {
            throw KEMException.internalError("Invalid category of k found.", term);
        }
    }

    public static Sort lubSort(Sort leftSort, Sort rightSort, Sort expectedSort, HasLocation loc, Module mod) {
        if (leftSort == null && rightSort == null) {
            return expectedSort;
        } else if (leftSort == null) {
            return rightSort;
        } else if (rightSort == null) {
            return leftSort;
        }
        return lub(Arrays.asList(leftSort, rightSort), expectedSort, loc, mod);
    }

    private Production production(KApply term) {
        if (term.klabel() instanceof KVariable) {
          throw KEMException.internalError("KORE does not yet support KLabel variables.", term);
        }
        scala.collection.Set<Production> prods = mod.productionsFor().apply(((KApply) term).klabel().head());
        if (prods.size() != 1) {
          throw KEMException.compilerError("Could not find production for KApply with label " + term.klabel(), term);
        }
        return prods.head();
    }

    private static Sort lub(Collection<Sort> entries, Sort expectedSort, HasLocation loc, Module mod) {
        assert !entries.isEmpty();
        entries = new HashSet<>(entries);
        Collection<Sort> filteredEntries = entries.stream().filter(s -> !s.name().equals(SORTPARAM_NAME)).collect(Collectors.toList());
        if (filteredEntries.isEmpty()) { // if all sorts are parameters, take the first
            return entries.iterator().next();
        }
        Set<Sort> bounds = upperBounds(filteredEntries, mod);
        if (expectedSort != null && !expectedSort.name().equals(SORTPARAM_NAME) && !expectedSort.equals(Sorts.KItem()) && !expectedSort.equals(Sorts.K())) {
            bounds.removeIf(s -> !mod.subsorts().lessThanEq(s, expectedSort));
        }
        Set<Sort> lub = mod.subsorts().minimal(bounds);
        if (lub.size() != 1) {
            throw KEMException.internalError("Could not compute least upper bound for rewrite sort. Possible candidates: " + lub, loc);
        }
        return lub.iterator().next();
    }

    private static Set<Sort> upperBounds(Collection<Sort> bounds, Module mod) {
        Set<Sort> maxs = new HashSet<>();
    nextsort:
        for (Sort sort : iterable(mod.definedSorts())) { // for every declared sort
            // Sorts at or below KBott, or above K, are assumed to be
            // sorts from kast.k representing meta-syntax that is not a real sort.
            // This is done to prevent variables from being inferred as KBott or
            // as KList.
            if (mod.subsorts().lessThanEq(sort, Sorts.KBott()))
                continue;
            if (mod.subsorts().greaterThan(sort, Sorts.K()))
                continue;
            for (Sort bound : bounds)
                if (!mod.subsorts().lessThanEq(bound, sort))
                    continue nextsort;
            maxs.add(sort);
        }
        return maxs;
    }

    private Sort freshSortParam() {
        return Sort(SORTPARAM_NAME, Sort("Q" + freshSortParamCounter++));
    }
}
