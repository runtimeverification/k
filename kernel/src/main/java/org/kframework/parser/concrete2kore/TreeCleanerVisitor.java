// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete2kore;

import org.kframework.parser.*;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Optional;

/**
 * Remove parsing artifacts such as single element ambiguities.
 */
// TODO: simplify by removing leftover "null" checks and recheck this code
public class TreeCleanerVisitor extends Transformer {

    @Override
    public Optional<Term> apply(TermCons tc) {
        Optional<Term> vis;
        if (tc.production().klabel().isEmpty())
            vis = apply(tc.items().get(0));
        else {
            // invalidate the hashCode cache
//            tc.invalidateHashCode();
            vis = super.apply(tc);
        }
        return vis;
    }

    @Override
    public Optional<Term> apply(KList node) {
        mapChildren(node);
        if(node.items().size() == 1)
            return Optional.of(node.items().get(0));
        else
            return Optional.of(node);
    }

    @Override
    public Optional<Term> apply(Ambiguity node) {
        ParseFailedException exception = new ParseFailedException(new KException(
                ExceptionType.ERROR, KExceptionGroup.INNER_PARSER,
                "Parse forest contains no trees!", node.getSource(), node.getLocation()));
        java.util.Set<Term> terms = new HashSet<>();
        for (Term t : node.getContents()) {
            ASTNode result;
            try {
                result = this.visitNode(t);
                terms.add((Term) result);
            } catch (ParseFailedException e) {
                exception = e;
            }
        }

        if (terms.isEmpty())
            throw exception;
        if (terms.size() == 1) {
            return terms.iterator().next();
        }
        node.setContents(new ArrayList<>(terms));
        return visit((Term) node, null);
    }
}
