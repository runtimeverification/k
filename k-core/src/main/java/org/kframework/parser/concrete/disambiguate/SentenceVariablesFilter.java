// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.*;
import org.kframework.kil.visitors.ParseForestTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
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
public class SentenceVariablesFilter extends ParseForestTransformer {
    private boolean config = false;

    public SentenceVariablesFilter(org.kframework.kil.loader.Context context) {
        super("Sentence Variable Filter", context);
    }

    @Override
    public ASTNode visit(Configuration cfg, Void _) throws ParseFailedException {
        config = true;
        return super.visit(cfg, _);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context cfg, Void _) throws ParseFailedException {
        config = false;
        return super.visit(cfg, _);
    }

    @Override
    public ASTNode visit(Rule cfg, Void _) throws ParseFailedException {
        config = false;
        return super.visit(cfg, _);
    }

    @Override
    public ASTNode visit(Syntax cfg, Void _) throws ParseFailedException {
        config = false;
        return cfg;
    }

    @Override
    public ASTNode visit(TermCons tc, Void _) throws ParseFailedException {
        super.visit(tc, _);
        if (tc.getProduction().isSyntacticSubsort()) {
            if (tc.getContents().get(0) instanceof Variable) {
                return tc.getContents().get(0);
            }
        }
        return tc;
    }

    @Override
    public ASTNode visit(Variable var, Void _) throws ParseFailedException {
        if (config) {
            if (!var.getName().startsWith("$")) {
                String msg = "In the configuration you can only have external variables, not: '" + var.getName() + "' (starts with '$').";
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, var.getSource(), var.getLocation());
                throw new VariableTypeClashException(kex);
            }
        } else {
            if (var.getName().startsWith("$")) {
                String msg = "You can have external variables only in the configuration: '" + var.getName() + "' (starts with '$').";
                KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, var.getSource(), var.getLocation());
                throw new VariableTypeClashException(kex);
            }
        }
        return var;
    }
}
