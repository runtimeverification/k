// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;


import com.google.common.collect.Sets;
import org.kframework.POSet;
import org.kframework.builtin.Sorts;
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
import org.kframework.parser.concrete2kore.generator.UserList;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.pcollections.ConsPStack;
import scala.Tuple2;
import scala.util.Either;
import scala.util.Right;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * Transformer class adding the implicit terminator (.List{"<klabel>"}) to user defined lists.
 */
public class AddEmptyLists extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {

    private final Module m;
    private final POSet<Sort> subsorts;
    private final scala.collection.Set<Sort> listSorts;
    private final Map<String, List<UserList>> lists;

    public AddEmptyLists(Module m) {
        this.m = m;
        subsorts = m.subsorts();
        listSorts = m.listSorts();
        lists = UserList.getLists(mutable(m.sentences())).stream().collect(Collectors.groupingBy(p -> p.sort));
    }

    @Override
    public Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> apply(TermCons tc) {
        Production p = tc.production();
        java.util.Set<ParseFailedException> warnings = new HashSet<>();

        List<Term> reversed = tc.items().stream().collect(Collectors.toList());
        Collections.reverse(reversed); // TermCons with PStack requires the elements to be in the reverse order
        Iterator<Term> items = reversed.iterator();
        List<Term> newItems = new LinkedList<>();
        boolean changed = false;

        final String tcLabelName = tc.production().klabel().get().name();
        // Never add a list wrapper between a sort annotation and the annotated term
        if (tcLabelName.equals("#SyntacticCast")
                || tcLabelName.startsWith("#SemanticCastTo")
                || tcLabelName.equals("#InnerCast")) {
            return super.apply(tc);
        }

        for (ProductionItem pi : mutable(p.items())) {
            if (!(pi instanceof NonTerminal))
                continue;

            Sort expectedSort = ((NonTerminal) pi).sort();
            ProductionReference child = (ProductionReference) items.next();
            Sort childSort = getSort(child);
            if (listSorts.contains(expectedSort) &&
                    !(subsorts.lessThanEq(childSort, expectedSort) && listSorts.contains(childSort))) {
                final boolean isBracket = child.production().att().contains("bracket");
                if (isBracket
                        || (child.production().klabel().isDefined()
                        && child.production().klabel().get().name().equals("#KRewrite"))) {
                    newItems.add(child);
                } else if (childSort.equals(Sorts.K()) || !subsorts.lessThan(childSort, expectedSort)) {
                    String msg = "Found sort '" + childSort + "' where list sort '" + expectedSort + "' was expected. Moving on.";
                    warnings.add(new ParseFailedException(
                            new KException(KException.ExceptionType.HIDDENWARNING, KException.KExceptionGroup.LISTS, msg, child.source().get(), child.location().get())));
                    newItems.add(child);
                } else {
                    UserList ul = lists.get(expectedSort.name()).get(0);
                    TermCons terminator = TermCons.apply(ConsPStack.empty(), ul.pTerminator, child.location(), child.source());
                    // TermCons with PStack requires the elements to be in the reverse order
                    TermCons newTc = TermCons.apply(ConsPStack.from(Arrays.asList(terminator, child)), ul.pList, child.location(), child.source());
                    newItems.add(newTc);
                    changed = true;
                }
            } else {
                newItems.add(child);
            }
        }

        if (changed) {
            Collections.reverse(newItems); // TermCons with PStack requires the elements to be in the reverse order
            tc = TermCons.apply(ConsPStack.from(newItems), tc.production(), tc.location(), tc.source());
        }
        if (!warnings.isEmpty()) {
            Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rez = super.apply(tc);
            return new Tuple2<>(Right.apply(rez._1().right().get()), Sets.union(warnings, rez._2()));
        } else {
            return super.apply(tc);
        }
    }

    private Sort getSort(ProductionReference child) {
        if ((child instanceof TermCons) &&
                child.production().klabel().isDefined()) {
            KLabel label = child.production().klabel().get();
            if (label.name().equals("#KApply")) {
                Term labelTerm = ((TermCons) child).get(0);
                Optional<KLabel> optLabel = klabelFromTerm(labelTerm);
                if (optLabel.isPresent() && m.productionsFor().contains(optLabel.get())) {
                    Collection<Production> productions = mutable(m.productionsFor().get(optLabel.get()).get());
                    List<Term> rawArgs = lowerKList(((TermCons) child).get(1));
                    assert rawArgs.stream().allMatch(ProductionReference.class::isInstance);
                    @SuppressWarnings("unchecked") List<ProductionReference> args = (List<ProductionReference>) (List) rawArgs;
                    List<Sort> childSorts = args.stream().map(this::getSort).collect(Collectors.toList());
                    if (!childSorts.contains(Sort("KList"))) { // try to exclude non-concrete lists
                        List<Production> validProductions = new ArrayList<>();
                    nextprod:
                        for (Production prod : productions) {
                            Iterator<Sort> sortIter = childSorts.iterator();
                            for (ProductionItem item : iterable(prod.items())) {
                                if (!(item instanceof NonTerminal))
                                    continue;
                                if (!sortIter.hasNext()) {
                                    // production arity too high
                                    continue nextprod;
                                }
                                if (!subsorts.lessThanEq(sortIter.next(), ((NonTerminal) item).sort())) {
                                    // production can't accept this argument
                                    continue nextprod;
                                }
                            }
                            if (sortIter.hasNext()) {
                                // production arity too low
                                continue;
                            }
                            validProductions.add(prod);
                        }
                        productions = validProductions;
                        Optional<Sort> leastSort = least(productions.stream().map(Production::sort).collect(Collectors.toList()));
                        if (leastSort.isPresent()) {
                            return leastSort.get();
                        }
                    } else {
                        Optional<Sort> greatestSort = greatest(productions.stream().map(Production::sort).collect(Collectors.toList()));
                        if (greatestSort.isPresent()) {
                            return greatestSort.get();

                        }
                    }
                }
            }
        }
        return child.production().sort();
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
            if (labelCon.production().sort().name().equals("KLabel")) {
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
