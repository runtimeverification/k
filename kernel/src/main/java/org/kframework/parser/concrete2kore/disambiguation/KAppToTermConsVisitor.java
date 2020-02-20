// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import org.pcollections.PStack;
import scala.collection.immutable.Set$;
import scala.util.Either;
import scala.util.Left;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;


/**
 * Transform the KApps found in a term into the corresponding TermCons so type checking and
 * variable type inference takes place correctly. Must be applied between type inference and
 * priority filter.
 */
public class KAppToTermConsVisitor extends SetsTransformerWithErrors<KEMException> {

    private final Module mod;
    public KAppToTermConsVisitor(Module mod) {
        super();
        this.mod = mod;
    }

    @Override
    public Either<java.util.Set<KEMException>, Term> apply(TermCons tc) {
        assert tc.production() != null : this.getClass() + ":" + " production not found." + tc;
        if (tc.production().klabel().isDefined() && tc.production().klabel().get().name().equals("#KApply")) {
            if (!(tc.get(0) instanceof Constant) || !((Constant) tc.get(0)).production().sort().equals(Sorts.KLabel()))
                // TODO: maybe return a hidden warning?
                return super.apply(tc); // don't do anything if the label is not a token KLabel (in case of variable or casted variable)
            Constant kl = (Constant) tc.get(0);
            PStack<Term> items = flattenKList(tc.get(1));
            String klvalue = kl.value();
            try { klvalue = StringUtil.unescapeKoreKLabel(kl.value()); } catch (IllegalArgumentException e) { /* ignore */ } // if possible, unescape
            Set<Production> prods = mutable(mod.productionsFor().get(KLabel(klvalue))
                    .getOrElse(Set$.MODULE$::emptyInstance)
                    .filter(x -> ((Production) x).arity() == items.size()).toSet());
            if (prods.size() == 0) {
                String msg = "Could not find any production with arity " + items.size() + " for label " + kl.value();
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, kl)));
            } else if (prods.size() == 1)
                return super.apply(TermCons.apply(items, prods.iterator().next(), tc.location(), tc.source()));
            else {
                // instantiate all labels found and let the type checker filter them out
                Set<Term> tcs = new HashSet<>();
                for (Production prd : prods)
                    tcs.add(TermCons.apply(items, prd, tc.location(), tc.source()));
                return super.apply(Ambiguity.apply(tcs, tc.location(), tc.source()));
            }
        }
        return super.apply(tc);
    }

    /**  Recurse under #KList and flatten all the terms */
    private static PStack<Term> flattenKList(Term t) {
        if (t instanceof Ambiguity) {
            Ambiguity amb = (Ambiguity) t;
            // prefer KList if they exist, otherwise return t
            List<PStack<Term>> klists = amb.items().stream()
                    .filter(x -> x instanceof TermCons
                            && ((TermCons) x).production().klabel().isDefined()
                            && ((TermCons) x).production().klabel().get().name().equals("#KList"))
                    .map(KAppToTermConsVisitor::flattenKList)
                    .sorted((o1, o2) -> o2.size() - o1.size()).collect(Collectors.toList());

            // expecting the first ambiguity branch to have the highest amount of elements
            assert klists.size() <= 1 || klists.get(0).size() != klists.get(1).size():
                    KAppToTermConsVisitor.class + ":" + " unexpected ambiguity pattern found under KApp " + amb;
            if (klists.size() != 0)
                return klists.get(0);
        } else if (t instanceof TermCons) {
            TermCons tc = (TermCons) t;
            if (tc.production().klabel().isDefined() && tc.production().klabel().get().name().equals("#KList"))
                return flattenKList(tc.get(0)).plusAll(flattenKList(tc.get(1)));
            else if (tc.production().klabel().isDefined() && tc.production().klabel().get().name().equals("#EmptyKList"))
                return ConsPStack.empty();
        }
        return ConsPStack.singleton(t);
    }
}
