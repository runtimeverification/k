// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
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
import org.kframework.kore.TransformK;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import static org.kframework.Collections.iterable;

public class AddSortInjections {

    private final Module mod;
    private final Map<KLabel, KLabel> collectionFor;

    public AddSortInjections(Module mod) {
        this.mod = mod;
        this.collectionFor = ConvertDataStructureToLookup.collectionFor(mod);
    }

    public K addInjections(K term) {
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
        }.apply(term)) {
            term = KRewrite(RewriteToTop.toLeft(term), RewriteToTop.toRight(term));
        }
        Sort topSort = sort(term, Sorts.K());
        K result = addInjections(term, topSort);
        return result;
    }

    public boolean collectionIsMap(KLabel collectionLabel) {
        return mod.attributesFor().apply(collectionLabel).contains(Attribute.COMMUTATIVE_KEY)
                && !mod.attributesFor().apply(collectionLabel).contains(Attribute.IDEMPOTENT_KEY)
                && !mod.attributesFor().apply(collectionLabel).contains(Att.bag());
    }

    public K addInjections(K term, Sort expectedSort) {
        Sort actualSort = sort(term, expectedSort);
        if (actualSort == null) {
            actualSort = expectedSort;
        }
        if (actualSort.equals(expectedSort)) {
            return visitChildren(term, expectedSort, actualSort);
        } else if (expectedSort.equals(Sorts.K())) {
            if (actualSort.equals(Sorts.KItem())) {
                return KSequence(visitChildren(term, Sorts.KItem(), actualSort));
            } else {
                return KSequence(KApply(KLabel("inj", actualSort, Sorts.KItem()), KList(visitChildren(term, Sorts.KItem(), actualSort)), Att.empty().add(Sort.class, Sorts.KItem())));
            }
        } else {
            String hookAtt = mod.sortAttributesFor().get(expectedSort).getOrElse(() -> Att()).getOptional("hook").orElse("");
            if (hookAtt.equals("MAP.Map") || hookAtt.equals("SET.Set") || hookAtt.equals("LIST.List")) {
                for (KLabel collectionLabel : collectionFor.keySet()) {
                    Optional<String> wrapElement = mod.attributesFor().apply(collectionLabel).getOptional("wrapElement");
                    if (wrapElement.isPresent()) {
                        KLabel wrappedLabel = KLabel(wrapElement.get());
                        KLabel elementLabel = KLabel(mod.attributesFor().apply(collectionLabel).get("element"));
                        KApply k = (KApply)term;
                        if (k.klabel().equals(wrappedLabel)) {
                            if (collectionIsMap(collectionLabel)) {
                                // Map
                                return KApply(elementLabel, KList(k.klist().items().get(0), visitChildren(k, expectedSort, actualSort)), Att.empty().add(Sort.class, expectedSort));
                            } else {
                                return KApply(elementLabel, KList(visitChildren(k, expectedSort, actualSort)), Att.empty().add(Sort.class, expectedSort));
                            }
                        }
                    }
                }
                throw new AssertionError();
            } else {
                return KApply(KLabel("inj", actualSort, expectedSort), KList(visitChildren(term, expectedSort, actualSort)), Att.empty().add(Sort.class, expectedSort));
            }
        }
    }

    private K visitChildren(K term, Sort parentSort, Sort actualSort) {
        Att att = term.att().add(Sort.class, actualSort);
        if (term instanceof KApply) {
            KApply kapp = (KApply)term;
            if (kapp.klabel().name().equals("inj")) {
                return term;
            }
            Production prod = production(kapp);
            List<K> children = new ArrayList<>();
            Set<Integer> polyPositions = Collections.emptySet();
            if (prod.att().contains("poly")) {
                List<Set<Integer>> poly = RuleGrammarGenerator.computePositions(prod);
                for (Set<Integer> positions : poly) {
                    if (positions.contains(0)) {
                        polyPositions = positions;
                    }
                }
            }
            for (int i = 0; i < kapp.items().size(); i++) {
                Sort expectedSort = prod.nonterminal(i).sort();
                if (polyPositions.contains(i + 1)) {
                    expectedSort = actualSort;
                }
                K child = kapp.items().get(i);
                children.add(addInjections(child, expectedSort));
            }
            return KApply(kapp.klabel(), KList(children), att);
        } else if (term instanceof KRewrite) {
            KRewrite rew = (KRewrite) term;
            return KRewrite(addInjections(rew.left(), actualSort), addInjections(rew.right(), actualSort), att);
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
                    children.add(addInjections(child, Sorts.K()));
                } else {
                    children.add(addInjections(child, Sorts.KItem()));
                }
            }
            return KSequence(children, att);
        } else if (term instanceof KAs) {
            KAs kas = (KAs)term;
            return KAs(addInjections(kas.pattern(), actualSort), kas.alias(), att);
        } else {
            throw KEMException.internalError("Invalid category of k found.", term);
        }
    }

    public Sort sort(K term, Sort expectedSort) {
        if (term instanceof KApply) {
            KApply kapp = (KApply)term;
            if (kapp.klabel().name().equals("inj")) {
                return kapp.klabel().params().apply(1);
            }
            Production prod = production(kapp);
            if (prod.att().contains("poly")) {
                List<Set<Integer>> poly = RuleGrammarGenerator.computePositions(prod);
                for (Set<Integer> positions : poly) {
                    if (positions.contains(0)) {
                        Set<Integer> otherPositions = new HashSet<>(positions);
                        otherPositions.remove(0);
                        Set<Sort> children = new HashSet<>();
                        for (int position : otherPositions) {
                            children.add(sort(kapp.items().get(position-1), expectedSort));
                        }
                        children.remove(null);
                        if (children.size() == 0) {
                            return expectedSort;
                        }
                        return lub(children, term);
                    }
                }
            }
            return production((KApply)term).sort();
        } else if (term instanceof KRewrite) {
            KRewrite rew = (KRewrite)term;
            Sort leftSort = sort(rew.left(), expectedSort);
            Sort rightSort = sort(rew.right(), expectedSort);
            return lubSort(leftSort, rightSort, expectedSort, term);
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
            return lubSort(patternSort, rightSort, expectedSort, term);
        } else {
            throw KEMException.internalError("Invalid category of k found.", term);
        }
    }

    private Sort lubSort(Sort leftSort, Sort rightSort, Sort expectedSort, HasLocation loc) {
        if (leftSort == null && rightSort == null) {
            return expectedSort;
        } else if (leftSort == null) {
            return rightSort;
        } else if (rightSort == null) {
            return leftSort;
        }
        return lub(Arrays.asList(leftSort, rightSort), loc);
    }

    private Production production(KApply term) {
        scala.collection.Set<Production> prods = mod.productionsFor().apply(((KApply) term).klabel());
        if (prods.size() != 1) {
          throw KEMException.compilerError("Could not find production for KApply with label " + term.klabel(), term);
        }
        return prods.head();
    }

    private Sort lub(Collection<Sort> entries, HasLocation loc) {
        Set<Sort> bounds = upperBounds(entries);
        Set<Sort> lub = mod.subsorts().minimal(bounds);
        if (lub.size() != 1) {
            throw KEMException.internalError("Could not compute least upper bound for rewrite sort.", loc);
        }
        return lub.iterator().next();
    }

    private Set<Sort> upperBounds(Collection<Sort> bounds) {
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

}
