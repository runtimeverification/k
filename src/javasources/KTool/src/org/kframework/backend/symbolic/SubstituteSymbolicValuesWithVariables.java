package org.kframework.backend.symbolic;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 11/21/13
 * Time: 11:37 AM
 * Replace symbolic values with variable names when possible.
 */
public class SubstituteSymbolicValuesWithVariables extends CopyOnWriteTransformer {
    public SubstituteSymbolicValuesWithVariables(Context context) {
        super("Replace symbolic values with variable names", context);
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {

        if (node.getLabel().toString().contains(AddSymbolicK.getSymbolicConstructorPrefix())) {

            String sort = node.getLabel().toString().substring(AddSymbolicK.getSymbolicConstructorPrefix().length());

            Term child = ((KList)node.getChild()).getContents().get(0);
            if (child instanceof KApp) {
                Term token = ((KApp) child).getLabel();
                if (token instanceof GenericToken) {
                    GenericToken gToken = (GenericToken) token;
                    if (gToken.tokenSort().equals("#Id")) {
                        Variable v = new Variable(gToken.value(), sort);
                        return v;
                    }
                }
            }

        }

        return super.transform(node);    //To change body of overridden methods use File | Settings | File Templates.
    }
}
