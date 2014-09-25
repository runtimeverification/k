// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.symbolic;

import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.KApp;
import org.kframework.kil.Sort;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 * Replace data constants with symbolic values and
 * store the pair (Variable,Constant) into a map.
 *
 * @author andreiarusoaie
 */
public class ConstantsReplaceTransformer extends CopyOnWriteTransformer {
    private Map<Variable, KApp> generatedSV;

    public ConstantsReplaceTransformer(String name, Context context) {
        super("Replace Constants", context);
        generatedSV = new HashMap<Variable, KApp>();
    }

    @Override
    public ASTNode visit(KApp node, Void _)  {

        if (node.getLabel() instanceof Token) {
//            Token token = ((Token) node.getLabel());
            Variable newVar = Variable.getFreshVar(Sort.K);
            generatedSV.put(newVar, node);
            return newVar;
        }

        return super.visit(node, _);
    }

    public Map<Variable, KApp> getGeneratedSV() {
        return generatedSV;
    }
}
