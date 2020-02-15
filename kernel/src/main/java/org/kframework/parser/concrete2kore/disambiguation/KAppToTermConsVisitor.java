// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore.disambiguation;

import com.google.common.collect.Sets;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.SetsTransformerWithErrors;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KEMException;
import org.pcollections.ConsPStack;
import org.pcollections.PStack;
import scala.collection.Seq;
import scala.util.Either;
import scala.util.Left;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;


/**
 * Transform the KApps found in a term into the corresponding TermCons so type checking and
 * variable type inference takes place correctly. Must be applied after priority filter but
 * before type inference.
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
            Constant kl = (Constant) tc.items().get(1);
            if (!kl.production().sort().equals(Sorts.KLabel())) {
                String msg = "Expected klabel constant in KApp.";
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, kl)));
            }
            // check if the label is defined and signature is unique
            if (mod.productionsFor().get(KLabel(kl.value())).isEmpty()) {
                String msg = "Could not find production for label " + kl.value();
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, kl)));
            } else if (mod.productionsFor().get(KLabel(kl.value())).get().size() > 1
                    // only interested in the signatures to match
                    && !isSignatureEqual(mutable(mod.productionsFor().get(KLabel(kl.value())).get()))) {
                String msg = "Found multiple productions for label " + kl.value();
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, kl)));
            }
            Production prd = mod.productionsFor().get(KLabel(kl.value())).get().head();
            PStack<Term> items = flattenKList(tc.items().get(0));
            if (items.size() != prd.arity()) {
                String msg = "Expected arity " + prd.arity() + " but found " + items.size() + " for label " + kl.value();
                return Left.apply(Sets.newHashSet(KEMException.innerParserError(msg, tc)));
            }
            return super.apply(TermCons.apply(items, prd, tc.location(), tc.source()));
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
                return flattenKList(tc.items().get(1)).plusAll(flattenKList(tc.items().get(0)));
            else if (tc.production().klabel().isDefined() && tc.production().klabel().get().name().equals("#EmptyKList"))
                return ConsPStack.empty();
        }
        return ConsPStack.singleton(t);
    }

    /** Check if the signature of all the productions from the set are the same */
    private static boolean isSignatureEqual(Set<Production> prods) {
        Production head = prods.iterator().next();
        Seq<ProductionItem> items = (Seq<ProductionItem>) head.items().filter(x -> x instanceof NonTerminal);
        for (Production p : prods) {
            if (!head.params().sameElements(p.params())) return false;
            if (!head.sort().equals(p.sort())) return false;
            if (head.arity() != p.arity()) return false;
            if (items.sameElements((Seq<ProductionItem>) p.items().filter(x -> x instanceof NonTerminal))) return false;
        }
        return true;
    }
}
