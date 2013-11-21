package org.kframework.backend.symbolic;

import org.kframework.compile.transformers.AddSymbolicK;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;

/**
 * Created with IntelliJ IDEA.
 * User: andrei.arusoaie
 * Date: 11/20/13
 * Time: 2:11 PM
 * To change this template use File | Settings | File Templates.
 */
public class SubstituteFreshVariablesWithSymbolic extends CopyOnWriteTransformer{

    public SubstituteFreshVariablesWithSymbolic(Context context) {
        super("Replace variables in programs with symbolic values", context);
    }

    @Override
    public ASTNode transform(org.kframework.kil.Variable node) throws TransformerException {

        if (!MetaK.isDataSort(node.getSort())) {
            String msg = "Variable " + node + " is not of sort builtin.";
            throw new TransformerException(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, msg, node.getFilename().trim(), node.getLocation()));
        }

        return KApp.of(KLabelConstant.of(AddSymbolicK.symbolicConstructor(node.getSort())), Token.kAppOf("#Id", node.getName()));
//        return IntBuiltin.kAppOf(10);
    }
}
