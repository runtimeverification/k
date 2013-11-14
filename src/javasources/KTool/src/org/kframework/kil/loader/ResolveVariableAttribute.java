package org.kframework.kil.loader;

import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.GenericToken;
import org.kframework.kil.KApp;
import org.kframework.kil.Token;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Created with IntelliJ IDEA.
 * User: Andrei
 * Date: 14.11.2013
 * Time: 10:37
 * To change this template use File | Settings | File Templates.
 */
public class ResolveVariableAttribute extends CopyOnWriteTransformer {
    public ResolveVariableAttribute(Context context) {
        super("Resolve 'variable' attribute", context);
    }

    @java.lang.Override
    public org.kframework.kil.ASTNode transform(KApp kapp) throws TransformerException {
        if (kapp.getLabel() instanceof Token) {
            Token node = (Token) kapp.getLabel();

            if (context.variableTokenSorts.contains(node.tokenSort()))
                return new org.kframework.kil.Variable(node.value(), node.tokenSort());
        }
        return super.transform(kapp);    //To change body of overridden methods use File | Settings | File Templates.
    }
}
