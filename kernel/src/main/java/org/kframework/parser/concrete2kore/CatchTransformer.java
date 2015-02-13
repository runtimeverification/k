// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;


import org.kframework.parser.Ambiguity;
import org.kframework.parser.Constant;
import org.kframework.parser.KList;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.TermCons;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.ParseFailedException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Base class Transformer used by the front-end to filter out ambiguities in
 * the DAG returned by the parser. It matches on every node based on the class hierarchy
 * from the most general to the most specialized.
 * The Ambiguity node is special since every call to visit a child is surrounded by a
 * try/catch statement, which captures errors thrown by the child visitor. If such an error
 * occurs, then the child is eliminated from the tree.
 *
 * This a lightweight wiring mechanism, and error handling is isolated greatly.
 */
public class CatchTransformer {
    Map<Term, Term> visited = new HashMap<>();
    public Term apply(Term t) throws ParseFailedException {
        if (cache() && visited.containsKey(t))
                return visited.get(t);
        Term rez;
        if (t instanceof Ambiguity) {
            rez = apply((Ambiguity) t);
        } else if (t instanceof KList) {
            rez = apply((KList) t);
        } else if (t instanceof ProductionReference) {
            rez = apply((ProductionReference) t);
        } else {
            throw new RuntimeException("Unexpected term type: " + t.getClass());
        }
        if (cache())
            visited.put(t, rez);
        return rez;
    }

    public Term apply(ProductionReference p) throws ParseFailedException {
        if (p instanceof TermCons) {
            return apply((TermCons) p);
        } else if (p instanceof Constant) {
            return apply((Constant) p);
        } else {
            throw new RuntimeException("Unexpected term type: " + p.getClass());
        }
    }

    /**
     * Match on an ambiguity node and visit it's children.
     * If any exception happens while visiting a child, remove it from the list.
     * @param a Ambiguity node to visit.
     * @return  The same Ambiguity node if there are at least two children left, or one of the
     * children, whichever passes the filter tests.
     * @throws ParseFailedException if all the children failed to be visited.
     */
    public Term apply(Ambiguity a) throws ParseFailedException {
        ParseFailedException exception = new ParseFailedException(new KException(
                ExceptionType.ERROR, KExceptionGroup.INNER_PARSER,
                "Parse forest contains no trees!", null, null));
        java.util.Set<Term> terms = new HashSet<>();
        for (Term t : a.items()) {
            Term result;
            try {
                result = apply(t);
                terms.add(result);
            } catch (ParseFailedException e) {
                exception = e;
            }
        }
        if (terms.isEmpty())
            throw exception;
        if (terms.size() == 1) {
            return apply(terms.iterator().next());
        }
        a.replaceChildren(terms);
        return a;
    }

    public Term apply(KList kl) throws ParseFailedException {
        for (int i = 0; i < kl.items().size(); i++) {
            kl.items().set(i, apply(kl.items().get(i)));
        }
        return kl;
    }

    public Term apply(TermCons tc) throws ParseFailedException {
        for (int i = 0; i < tc.items().size(); i++) {
            tc.items().set(i, apply(tc.items().get(i)));
        }
        return tc;
    }

    public Term apply(Constant c) throws ParseFailedException {
        return c;
    }

    protected boolean cache() {
        return false;
    }
}
