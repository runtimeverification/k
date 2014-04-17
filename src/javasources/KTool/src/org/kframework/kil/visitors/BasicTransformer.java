// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

/**
 * A transformer useful for processing parse forests (i.e. trees with ambiguity nodes).
 * 
 * To remove a branch of an ambiguity, throw {@link TransformerException} from the visit method.
 * @author dwightguth
 *
 */
public class BasicTransformer extends AbstractTransformer {

    public BasicTransformer(String name, Context context) {
        super(name, context);
    }

    @Override
    public ASTNode visit(Ambiguity node, Void _) throws TransformerException {
        TransformerException exception = new TransformerException(new KException(
                ExceptionType.ERROR, KExceptionGroup.INNER_PARSER, 
                "Parse forest contains no trees!", node.getFilename(), node.getLocation()));
        java.util.List<Term> terms = new ArrayList<>();
        for (Term t : node.getContents()) {
            ASTNode result;
            try {
                result = t.accept(this, null);
                terms.add((Term) result);
            } catch (TransformerException e) {
                exception = e;
            }
        }
        if (terms.isEmpty())
            throw exception;
        if (terms.size() == 1) {
            return terms.get(0);
        }
        node.setContents(terms);
        return visit((Term) node, null);
    }

    @Override
    public boolean visitChildren() {
        return true;
    }

    @Override
    public <T extends ASTNode> T copy(T original) {
        return original;
    }
    
}
