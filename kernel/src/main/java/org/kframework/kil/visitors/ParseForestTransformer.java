// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.kil.visitors;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

/**
 * A transformer useful for processing parse forests (i.e. trees with ambiguity nodes).
 *
 * To remove a branch of an ambiguity, throw {@link ParseFailedException} from the visit method.
 * @author dwightguth
 *
 */
public class ParseForestTransformer extends AbstractTransformer<ParseFailedException> {

    public ParseForestTransformer(String name, Context context) {
        super(name, context);
    }

    public ParseForestTransformer(String name, Context context,
                                  Definition currentDefinition, Module currentModule) {
        super(name, context, currentDefinition, currentModule);
    }

    @Override
    public ASTNode visit(Ambiguity node, Void _void) throws ParseFailedException {
        ParseFailedException exception = new ParseFailedException(new KException(
                ExceptionType.ERROR, KExceptionGroup.INNER_PARSER,
                "Parse forest contains no trees!", node.getSource(), node.getLocation()));
        java.util.List<Term> terms = new ArrayList<>();
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
