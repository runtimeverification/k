// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.inner.disambiguation;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.SafeTransformer;
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
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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
        if (tc.production().klabel().isDefined() && tc.production().klabel().get().equals(KLabels.KAPP)) {
            if (!(tc.get(0) instanceof Constant) || !((Constant) tc.get(0)).production().sort().equals(Sorts.KLabel()))
                // TODO: remove check once the java backend is no longer supported.
                return super.apply(tc); // don't do anything if the label is not a token KLabel (in case of variable or casted variable)
            Constant kl = (Constant) tc.get(0);
            String klvalue = kl.value();
            try { klvalue = StringUtil.unescapeKoreKLabel(kl.value()); } catch (IllegalArgumentException e) { /* ignore */ } // if possible, unescape
            Set<Production> prods = mutable(mod.productionsFor().get(KLabel(klvalue))
                    .getOrElse(Set$.MODULE$::emptyInstance).toSet());
            Set<Term> sol = new HashSet<>();
            Term t = new PushTopAmbiguityUp2().apply(tc.get(1));
            Stream<Term> uppedAmb = t instanceof Ambiguity ? ((Ambiguity) t).items().stream() : Lists.newArrayList(t).stream();
            Map<Integer, List<PStack<Term>>> flattKLists = uppedAmb
                    .map(KAppToTermConsVisitor::flattenKList)
                    .collect(Collectors.groupingBy(PStack::size));
            for (Production prd : prods)
                for (PStack<Term> terms : flattKLists.getOrDefault(prd.arity(), Lists.newArrayList()))
                    sol.add(TermCons.apply(terms, prd, tc.location(), tc.source()));

            if (sol.size() == 0) {
                String msg = "Could not find any suitable production for label " + kl.value();
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, kl)));
            } else if (sol.size() == 1) {
                return super.apply(sol.iterator().next());
            } else
                return super.apply(Ambiguity.apply(sol, tc.location(), tc.source()));
        }
        return super.apply(tc);
    }

    /**  Recurse under #KList and flatten all the terms */
    private static PStack<Term> flattenKList(Term t) {
        if (t instanceof Ambiguity) {
            assert false : KAppToTermConsVisitor.class + " expected all ambiguities to already be pushed to the top:\n" +
                    "   Source: " + ((Ambiguity) t).items().iterator().next().source().orElse(null) + "\n" +
                    "   Location: " + ((Ambiguity) t).items().iterator().next().location().orElse(null);
        } else if (t instanceof TermCons) {
            TermCons tc = (TermCons) t;
            if (tc.production().klabel().isDefined() && tc.production().klabel().get().equals(KLabels.KLIST))
                return flattenKList(tc.get(0)).plusAll(Lists.reverse(Lists.newArrayList(flattenKList(tc.get(1)))));
            else if (tc.production().klabel().isDefined() && tc.production().klabel().get().equals(KLabels.EMPTYKLIST))
                return ConsPStack.empty();
        }
        return ConsPStack.singleton(t);
    }

    // push ambiguities top so we can get easy access to KList
    private static class PushTopAmbiguityUp2 extends SafeTransformer {
        @Override
        public Term apply(TermCons tc) {
            if (tc.production().klabel().isDefined() && tc.production().klabel().get().head().equals(KLabels.KLIST)) {
                Term v0 = super.apply(tc.get(0));
                Term v1 = super.apply(tc.get(1));
                Set<Term> t0 = v0 instanceof Ambiguity ? ((Ambiguity) v0).items() : Sets.newHashSet(v0);
                Set<Term> t1 = v1 instanceof Ambiguity ? ((Ambiguity) v1).items() : Sets.newHashSet(v1);
                Set<Term> rez = Sets.newHashSet();
                for (Term t00 : t0)
                    for (Term t11 : t1)
                        rez.add(TermCons.apply(ConsPStack.singleton(t00).plus(t11), tc.production(), tc.location(), tc.source()));
                return Ambiguity.apply(rez, tc.location(), tc.source());
            }
            return tc;
        }
    }
}
