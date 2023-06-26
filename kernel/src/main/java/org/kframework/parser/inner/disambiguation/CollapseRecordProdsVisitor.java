// Copyright (c) K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Terminal;
import org.kframework.parser.Constant;
import org.kframework.parser.SafeTransformer;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import org.pcollections.PStack;
import scala.util.Either;
import scala.util.Left;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static org.kframework.Collections.*;

/**
 * Collapse the record productions from a cons list to a single term with all parameters.
 * Expecting the exact pattern of productions described in Production.recordProductions()
 */
public class CollapseRecordProdsVisitor extends SetsTransformerWithErrors<KEMException> {
    CollectVariableNames varNamesVis;
    // require the term before starting the visitor to make sure we generate unique variable names
    public CollapseRecordProdsVisitor(Term t) {
        varNamesVis = new CollectVariableNames();
        varNamesVis.apply(t);
    }

    @Override
    public Either<Set<KEMException>, Term> apply(TermCons tc) {
        if (tc.production().att().contains(Att.RECORD_PRD(), Production.class)) {
            Production origPrd = tc.production().att().get(Att.RECORD_PRD(), Production.class);
            Map<String, Term> children = new HashMap<>();
            TermCons iterator = tc;

            // find all named items
            while (iterator != null && iterator.production().att().contains(Att.RECORD_PRD(), Production.class)) {
                if (iterator.production().att().contains(Att.RECORD_PRD_MAIN()))
                    iterator = (TermCons) iterator.get(0);
                else if (iterator.production().att().contains(Att.RECORD_PRD_ONE())) {
                    String key = iterator.production().att().get(Att.RECORD_PRD_ONE());
                    children.put(key, iterator.get(0));
                    iterator = null;
                } else if (iterator.production().att().contains(Att.RECORD_PRD_ITEM())) {
                    String key = iterator.production().att().get(Att.RECORD_PRD_ITEM());
                    if (children.containsKey(key))
                        return Left.apply(Sets.newHashSet(KEMException.innerParserError("Duplicate record production key: " + key, tc)));
                    else
                        children.put(key, iterator.get(0));
                    iterator = null;
                } else if (iterator.production().att().contains(Att.RECORD_PRD_REPEAT())) {
                    TermCons item = (TermCons) iterator.get(1);
                    String key = item.production().att().get(Att.RECORD_PRD_ITEM());
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
                    String varName;
                    do { varName = "_" + nt.name().getOrElse(() -> "Gen") + uid++; } while (varNamesVis.varNames.contains(varName));
                    collapsedItems = collapsedItems.plus(Constant.apply(varName, anonVarPrd, tc.location(), tc.source()));
                }
            }
            TermCons collapsed = TermCons.apply(collapsedItems, origPrd, tc.location(), tc.source());
            return super.apply(collapsed);
        }
        return super.apply(tc);
    }

    private int uid = 0;

    private static class CollectVariableNames extends SafeTransformer {
        public Set<String> varNames = new HashSet<>();
        @Override
        public Term apply(Constant c) {
            if (c.production().sort().equals(Sorts.KVariable()))
                varNames.add(c.value());
            return super.apply(c);
        }
    }
}
