// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;


import org.kframework.POSet;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.kore.Sort;
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

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
/**
 * Transformer class adding the implicit terminator (.List{"<klabel>"}) to user defined lists.
 */
public class AddEmptyLists extends SetsGeneralTransformer<ParseFailedException, ParseFailedException> {

    private final Module m;
    private final POSet<Sort> subsorts;
    private final scala.collection.immutable.Set<Sort> listSorts;
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
        for (ProductionItem pi : mutable(p.items())) {
            if (!(pi instanceof NonTerminal))
                continue;

            Sort expectedSort = ((NonTerminal) pi).sort();
            ProductionReference child = (ProductionReference) items.next();
            Sort childSort = child.production().sort();
            if (child.production().att().contains("bracket")
                    || (child.production().klabel().isDefined()
                    && (child.production().klabel().get().name().equals("#KRewrite")
                        || tc.production().klabel().get().name().equals("#SyntacticCast")
                        || tc.production().klabel().get().name().startsWith("#SemanticCastTo")
                        || tc.production().klabel().get().name().equals("#InnerCast")))) {
                continue;
            }
            if (listSorts.contains(expectedSort) && !expectedSort.equals(childSort)) {
                if (childSort.equals(Sorts.K()) || !subsorts.lessThan(childSort, expectedSort)) {
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
            Tuple2<Either<Set<ParseFailedException>, Term>, Set<ParseFailedException>> rez = super.apply(tc);
            return new Tuple2<>(Right.apply(rez._1().right().get()), this.mergeWarnings(warnings, rez._2()));
        } else {
            return super.apply(tc);
        }
    }
}
