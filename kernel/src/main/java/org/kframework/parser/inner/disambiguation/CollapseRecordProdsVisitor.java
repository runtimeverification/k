// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.attributes.Att;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Terminal;
import org.kframework.kore.ADT;
import org.kframework.parser.Constant;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import org.pcollections.PStack;
import scala.util.Either;
import scala.util.Left;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import static org.kframework.Collections.*;

/**
 * Collapse the record productions from a cons list to a single term with all parameters.
 */
public class CollapseRecordProdsVisitor extends SetsTransformerWithErrors<KEMException> {
    @Override
    public Either<Set<KEMException>, Term> apply(TermCons tc) {
        if (tc.production().att().contains("recordPrd", Production.class)) {
            Production origPrd = tc.production().att().get("recordPrd", Production.class);
            Map<String, Term> children = new HashMap<>();
            TermCons iterator = tc;

            // find all named items
            while (iterator != null && iterator.production().att().contains("recordPrd", Production.class)) {
                if (iterator.production().att().contains("recordPrd-main"))
                    iterator = (TermCons) iterator.get(0);
                else if (iterator.production().att().contains("recordPrd-item")) {
                    String key = iterator.production().att().get("recordPrd-item");
                    if (children.containsKey(key))
                        return Left.apply(Sets.newHashSet(KEMException.innerParserError("Duplicate record production key: " + key, tc)));
                    else
                        children.put(key, iterator.get(0));
                    iterator = null;
                } else if (iterator.production().att().contains("recordPrd-repeat")) {
                    TermCons item = (TermCons) iterator.get(0);
                    String key = item.production().att().get("recordPrd-item");
                    if (children.containsKey(key))
                        return Left.apply(Sets.newHashSet(KEMException.innerParserError("Duplicate record production key: " + key, tc)));
                    else
                        children.put(key, item.get(0));
                    iterator = (TermCons) iterator.get(1);
                } else
                    iterator = null;
            }
            // construct expanded term with provided items and anonymous variables for missing ones
            PStack<Term> collapsedItems = ConsPStack.empty();
            for (NonTerminal nt : mutable(origPrd.nonterminals())) {
                if (nt.name().isDefined() && children.containsKey(nt.name().get()))
                    collapsedItems = collapsedItems.plus(children.get(nt.name().get()));
                else {
                    Production anonVarPrd = Production.apply(Seq(), new ADT.Sort("#KVariable", Seq()), Seq(Terminal.apply("_")), Att.empty());
                    collapsedItems = collapsedItems.plus(Constant.apply("_", anonVarPrd, tc.location(), tc.source()));
                }
            }
            TermCons collapsed = TermCons.apply(collapsedItems, origPrd);
            return super.apply(collapsed);
        }
        return super.apply(tc);
    }
}
