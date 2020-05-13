// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;


import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.AddSortInjections;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.kore.KLabel;
import org.kframework.kore.Sort;
import org.kframework.parser.Constant;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.SetsGeneralTransformer;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.definition.UserList;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Left;
import scala.util.Right;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

/**
 * Transformer class adding the implicit terminator (.List{"<klabel>"}) to user defined lists.
 */
public class AddEmptyLists extends SetsGeneralTransformer<KEMException, KEMException> {

    private final Module m;
    private final POSet<Sort> subsorts;
    private final scala.collection.Set<Sort> listSorts;
    private final Map<Sort, List<UserList>> lists;
    private final AddSortInjections inj;
    private Sort expectedSort;

    public AddEmptyLists(Module m, Sort expectedSort) {
        this.m = m;
        subsorts = m.subsorts();
        listSorts = m.listSorts();
        lists = UserList.getLists(mutable(m.sentences())).stream().collect(Collectors.groupingBy(p -> p.sort));
        inj = new AddSortInjections(m);
        this.expectedSort = expectedSort;
    }

    // instead of calling super.apply in the apply function below, we should
    // call this function, because super.apply does not correctly set the
    // expected sort before recursing, which means that we end up with
    // the wrong sort computations otherwise
    private Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> superApply(TermCons tc) {
        Set<KEMException> warns = new HashSet<>();
        TermCons orig = tc;
        Production p = inj.substituteProd(orig.production(), expectedSort, (i, fresh) -> getSort((ProductionReference)orig.get(i), fresh.nonterminals().apply(i).sort()), orig);
        for (int i = 0; i < tc.items().size(); i++) {
            Sort oldExpectedSort = expectedSort;
            expectedSort = p.nonterminals().apply(i).sort();
            Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> rez = apply(tc.get(i));
            warns.addAll(rez._2());
            if (rez._1().isLeft()) {
                return Tuple2.apply(rez._1(), warns);
            }
            tc = tc.with(i, rez._1().right().get());
            expectedSort = oldExpectedSort;
        }
        return Tuple2.apply(Right.apply(tc), warns);
    }

    @Override
    public Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> apply(TermCons tc) {
        TermCons orig = tc;
        Production p = inj.substituteProd(orig.production(), expectedSort, (i, fresh) -> getSort((ProductionReference)orig.get(i), fresh.nonterminals().apply(i).sort()), orig);
        java.util.Set<KEMException> warnings = new HashSet<>();

        List<Term> reversed = tc.items().stream().collect(Collectors.toList());
        Collections.reverse(reversed); // TermCons with PStack requires the elements to be in the reverse order
        Iterator<Term> items = reversed.iterator();
        List<Term> newItems = new LinkedList<>();
        boolean changed = false;

        if (tc.production().klabel().isDefined()) {
            final String tcLabelName = tc.production().klabel().get().name();
            // Never add a list wrapper between a sort annotation and the annotated term
            if (tcLabelName.equals("#SyntacticCast")
                    || tcLabelName.startsWith("#SemanticCastTo")
                    || tcLabelName.equals("#InnerCast")) {
                return superApply(tc);
            }
        }

        for (ProductionItem pi : mutable(p.items())) {
            if (!(pi instanceof NonTerminal))
                continue;
            Sort oldExpectedSort = expectedSort;
            expectedSort = ((NonTerminal)pi).sort();
            ProductionReference child = (ProductionReference) items.next();
            Sort childSort = getSort(child, expectedSort);
            if (listSorts.contains(expectedSort) &&
                    !(subsorts.lessThanEq(childSort, expectedSort) && listSorts.contains(childSort))) {
                final boolean isBracket = child.production().att().contains(Att.BRACKET());
                if (isBracket
                        || (child.production().klabel().isDefined()
                        && child.production().klabel().get().name().equals("#KRewrite"))) {
                    newItems.add(child);
                } else if (childSort.equals(Sorts.K()) || !subsorts.lessThan(childSort, expectedSort)) {
                    newItems.add(child);
                } else {
                    Set<Sort> least = subsorts.minimal(stream(listSorts).filter(s -> subsorts.greaterThanEq(lists.get(s).get(0).childSort, childSort) && subsorts.lessThanEq(s, expectedSort)).collect(Collectors.toList()));
                    if (least.size() != 1) {
                        String msg = "Overloaded term does not have a least sort. Possible sorts: " + least;
                        return new Tuple2<>(Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc))), warnings);
                    }
                    UserList ul = lists.get(least.iterator().next()).get(0);
                    Set<Sort> leastTerm = subsorts.minimal(stream(listSorts).filter(s -> subsorts.lessThanEq(s, expectedSort)).collect(Collectors.toList()));
                    if (leastTerm.size() != 1) {
                        String msg = "List terminator for overloaded term does not have a least sort. Possible sorts: " + leastTerm;
                        return new Tuple2<>(Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc))), warnings);
                    }
                    UserList ulTerm = lists.get(leastTerm.iterator().next()).get(0);
                    TermCons terminator = TermCons.apply(ConsPStack.empty(), ulTerm.pTerminator, child.location(), child.source());
                    // TermCons with PStack requires the elements to be in the reverse order
                    TermCons newTc = TermCons.apply(ConsPStack.from(Arrays.asList(terminator, child)), ul.pList, child.location(), child.source());
                    newItems.add(newTc);
                    changed = true;
                }
            } else {
                newItems.add(child);
            }
            expectedSort = oldExpectedSort;
        }

        if (changed) {
            Collections.reverse(newItems); // TermCons with PStack requires the elements to be in the reverse order
            tc = TermCons.apply(ConsPStack.from(newItems), tc.production(), tc.location(), tc.source());
        }
        if (!warnings.isEmpty()) {
            Tuple2<Either<Set<KEMException>, Term>, Set<KEMException>> rez = superApply(tc);
            return new Tuple2<>(Right.apply(rez._1().right().get()), Sets.union(warnings, rez._2()));
        } else {
            return superApply(tc);
        }
    }

    private Sort getSort(ProductionReference child, Sort expectedSort) {
        if (m.syntacticSubsorts().greaterThan(expectedSort, Sorts.K())) {
            expectedSort = Sorts.K();
        }
        return inj.substituteProd(child.production(), expectedSort, (i, fresh) -> getSort((ProductionReference)((TermCons)child).get(i), fresh.nonterminals().apply(i).sort()), child).sort();
    }

    /**
     * Returns an element of sorts which is related to and no
     * greater than every other element of sorts, if any exists.
     */
    private Optional<Sort> least(Iterable<Sort> sorts) {
        Iterator<Sort> iter = sorts.iterator();
        if (!iter.hasNext()) {
            return Optional.empty();
        }
        Sort min = iter.next();
        while (iter.hasNext()) {
            Sort next = iter.next();
            if (!subsorts.lessThanEq(min, next)) {
                // if min is unrelated to next, it can't be the least sort so
                // we also might as well switch
                min = next;
            }
        }
        for (Sort s : sorts) {
            if (!subsorts.lessThanEq(min, s)) {
                return Optional.empty();
            }
        }
        return Optional.of(min);
    }

    /**
     * Returns an element of sorts which is related to and no
     * less than every other element of sorts, if any exists.
     */
    private Optional<Sort> greatest(Iterable<Sort> sorts) {
        Iterator<Sort> iter = sorts.iterator();
        if (!iter.hasNext()) {
            return Optional.empty();
        }
        Sort max = iter.next();
        while (iter.hasNext()) {
            Sort next = iter.next();
            if (!subsorts.greaterThanEq(max, next)) {
                // if min is unrelated to next, it can't be the least sort so
                // we also might as well switch
                max = next;
            }
        }
        for (Sort s : sorts) {
            if (!subsorts.greaterThanEq(max, s)) {
                return Optional.empty();
            }
        }
        return Optional.of(max);
    }

    private Optional<KLabel> klabelFromTerm(Term labelTerm) {
        if (labelTerm instanceof Constant) {
            Constant labelCon = (Constant) labelTerm;
            if (labelCon.production().sort().equals(Sorts.KLabel())) {
                String labelVal = labelCon.value();
                if (labelVal.charAt(0) == '`') {
                    return Optional.of(KLabel(labelVal.substring(1, labelVal.length() - 1)));
                } else {
                    return Optional.of(KLabel(labelVal));
                }
            }
        }
        return Optional.empty();
    }

    private List<Term> lowerKList(Term listTerm) {
        List<Term> items = new ArrayList<>();
        lowerKListAcc(listTerm, items);
        return items;
    }

    private void lowerKListAcc(Term term, List<Term> items) {
        if (term instanceof TermCons) {
            TermCons cons = (TermCons) term;
            if (cons.production().klabel().isDefined()) {
                String labelName = cons.production().klabel().get().name();
                if (labelName.equals("#KList")) {
                    assert cons.items().size() == 2;
                    lowerKListAcc(cons.get(0), items);
                    lowerKListAcc(cons.get(1), items);
                    return;
                } else if (labelName.equals("#EmptyKList")) {
                    return;
                }
            }
        }
        items.add(term);
    }
}
