// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

import java.util.List;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 11/25/13
 * Time: 3:02 PM
 * Transform symbolic variables into K variables. This is done
 * only in the Maude symbolic backend.
 */
public class TokenVariableToSymbolic extends CopyOnWriteTransformer {
    public TokenVariableToSymbolic(Context context) {
        super("Transform symbolic values into tokens declared as 'variable'", context);
    }

    @Override
    public ASTNode visit(KApp node, Void _)  {
        if (node.getLabel().toString().startsWith(AddSymbolicK.getSymbolicConstructorPrefix())) {
            String sort = node.getLabel().toString().substring(AddSymbolicK.getSymbolicConstructorPrefix().length());
            List<Term> contents = ((KList) node.getChild()).getContents();
            if (!contents.isEmpty()) {
                Term child = contents.get(0);
                if (child instanceof KApp) {
                    Term token = ((KApp) child).getLabel();
                    if (token instanceof GenericToken) {
                        GenericToken gToken = (GenericToken) token;
                        if (gToken.tokenSort().equals(Sort.BUILTIN_ID)) {
                            Variable v = new Variable(gToken.value(), Sort.of(sort));
                            return v;
                        }
                    }
                }
            }
        }

        return super.visit(node, _);
    }
}

