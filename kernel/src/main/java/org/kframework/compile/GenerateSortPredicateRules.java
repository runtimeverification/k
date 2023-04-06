// Copyright (c) K Team. All Rights Reserved.
package org.kframework.compile;

import org.apache.commons.lang3.mutable.MutableBoolean;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
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

    private Module mod;
    private java.util.Set<Rule> predicateRules;

    public Module gen(Module mod) {
        this.mod = mod;
        predicateRules = stream(mod.rules()).filter(this::isPredicate).collect(Collectors.toSet());
        return Module(mod.name(), mod.imports(), (Set<Sentence>) mod.localSentences().$bar(stream(mod.allSorts())
                .flatMap(this::gen).collect(Collections.toSet())), mod.att());
    }

    private Stream<? extends Sentence> gen(Sort sort) {
        if (sort.equals(Sorts.K())) {
            return Stream.of(Rule(KRewrite(KApply(KLabel("is" + sort.toString()), KVariable("K")), BooleanUtils.TRUE), BooleanUtils.TRUE, BooleanUtils.TRUE));
        } else {
            List<Sentence> res = new ArrayList<>();
            res.add(Rule(KRewrite(KApply(KLabel("is" + sort.toString()), KVariable(sort.name(), Att().add(Sort.class, sort))), BooleanUtils.TRUE), BooleanUtils.TRUE, BooleanUtils.TRUE));
            res.add(Rule(KRewrite(KApply(KLabel("is" + sort.toString()), KVariable("K")), BooleanUtils.FALSE), BooleanUtils.TRUE, BooleanUtils.TRUE, Att().add(Att.OWISE())));
            return res.stream();
        }
    }

    private boolean isTruePredicate(Rule r) {
        return RewriteToTop.toRight(r.body()).equals(BooleanUtils.TRUE);
    }

    private boolean isPredicateFor(Rule r, Sort s) {
        Optional<Sort> sort = getPredicateSort(r);
        return sort.isPresent() && sort.get().equals(s);
    }

    private boolean isPredicate(Rule r) {
        return getPredicateSort(r).isPresent();
    }

    private Optional<Sort> getPredicateSort(Rule r) {
        KLabel topKLabel;
        Optional<Sort> sort;
        if (r.body() instanceof KApply) {
            topKLabel = ((KApply) r.body()).klabel();
            sort = mod.attributesFor().apply(topKLabel).getOptional(Att.PREDICATE(), Sort.class);
        } else if (r.body() instanceof KRewrite) {
            KRewrite rw = (KRewrite) r.body();
            if (rw.left() instanceof KApply) {
                topKLabel = ((KApply) rw.left()).klabel();
                sort = mod.attributesFor().apply(topKLabel).getOptional(Att.PREDICATE(), Sort.class);
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
            return Rule(KRewrite(KApply(KLabel("is" + s.toString()), ((KApply) left).klist()), BooleanUtils.TRUE), BooleanUtils.and(r.requires(), right), r.ensures(), r.att());
        } else {
            throw new IllegalArgumentException("not a predicate rule");
        }
    }
}
