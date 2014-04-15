// Copyright (C) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.visitors.exceptions.VariableTypeClashException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

/**
 * Remove meta-variables from the configuration.
 * 
 * @author radu
 * 
 */
public class SentenceVariablesFilter extends BasicTransformer {
    private boolean config = false;

    public SentenceVariablesFilter(org.kframework.kil.loader.Context context) {
        super("Sentence Variable Filter", context);
    }

    @Override
    public ASTNode visit(Configuration cfg, Void _) throws TransformerException {
        config = true;
        return super.visit(cfg, _);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context cfg, Void _) throws TransformerException {
        config = false;
        return super.visit(cfg, _);
    }

    @Override
    public ASTNode visit(Rule cfg, Void _) throws TransformerException {
        config = false;
        return super.visit(cfg, _);
    }

    @Override
    public ASTNode visit(Syntax cfg, Void _) throws TransformerException {
        config = false;
        return cfg;
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws TransformerException {
        super.visit(tc, _);
        if (tc.getProduction().isSubsort()) {
            if (tc.getContents().get(0) instanceof Variable) {
                return tc.getContents().get(0);
            }
        }
        return tc;
    }

    @Override
    public ASTNode visit(Variable var, Void _) throws TransformerException {
        if (config) {
            if (!var.getName().startsWith("$")) {
                String msg = "In the configuration you can only have external variables, not: '" + var.getName() + "' (starts with '$').";
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, var.getFilename(), var.getLocation());
                throw new VariableTypeClashException(kex);
            }
        } else {
            if (var.getName().startsWith("$")) {
                String msg = "You can have external variables only in the configuration: '" + var.getName() + "' (starts with '$').";
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, var.getFilename(), var.getLocation());
                throw new VariableTypeClashException(kex);
            }
        }
        return var;
    }
}
