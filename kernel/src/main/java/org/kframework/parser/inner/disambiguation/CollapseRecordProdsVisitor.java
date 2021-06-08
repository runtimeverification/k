// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Terminal;
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
 * Expecting the exact pattern of productions described in Production.recordProductions()
 */
public class CollapseRecordProdsVisitor extends SetsTransformerWithErrors<KEMException> {
    @Override
    public Either<Set<KEMException>, Term> apply(TermCons tc) {
        if (tc.production().att().contains(Att.RECORD_PRD(), Production.class)) {
            Production origPrd = tc.production().att().get(Att.RECORD_PRD(), Production.class);
            Map<String, Term> children = new HashMap<>();
            TermCons iterator = tc;

            // find all named items
            while (iterator != null && iterator.production().att().contains(Att.RECORD_PRD(), Production.class)) {
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
                    TermCons item = (TermCons) iterator.get(1);
                    String key = item.production().att().get("recordPrd-item");
                    if (children.containsKey(key))
                        return Left.apply(Sets.newHashSet(KEMException.innerParserError("Duplicate record production key: " + key, tc)));
                    else
                        children.put(key, item.get(0));
                    iterator = (TermCons) iterator.get(0);
                } else
                    iterator = null;
            }
            // construct expanded term with provided items and anonymous variables for missing ones
            PStack<Term> collapsedItems = ConsPStack.empty();
            for (NonTerminal nt : mutable(origPrd.nonterminals())) {
                if (nt.name().isDefined() && children.containsKey(nt.name().get()))
                    collapsedItems = collapsedItems.plus(children.get(nt.name().get()));
                else {
                    Production anonVarPrd = Production.apply(Seq(), Sorts.KVariable(), Seq(Terminal.apply("_[A-Z][A-Za-z0-9'_]*")), Att.empty());
                    // The name is required so disambiguation doesn't collapse the variables into the same term.
                    collapsedItems = collapsedItems.plus(Constant.apply("_" + nt.name().getOrElse(() -> "Gen") + uid++, anonVarPrd, tc.location(), tc.source()));
                }
            }
            TermCons collapsed = TermCons.apply(collapsedItems, origPrd, tc.location(), tc.source());
            return super.apply(collapsed);
        }
        return super.apply(tc);
    }

    private int uid = 0;
}
