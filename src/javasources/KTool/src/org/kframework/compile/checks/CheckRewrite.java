// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.kil.Configuration;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

public class CheckRewrite extends BasicVisitor {

    public CheckRewrite(Context context) {
        super(context);
    }

    private boolean inConfig = false;
    private boolean inRewrite = false;
    private boolean inSideCondition = false;
    private boolean inFunction = false;
    private int rewritesNo = 0;

    @Override
    public Void visit(Syntax node, Void _) {
        return null;
    }

    @Override
    public Void visit(Configuration node, Void _) {
        inConfig = true;
        super.visit(node, _);
        inConfig = false;
        return null;
    }

    @Override
    public Void visit(Rule node, Void _) {
        rewritesNo = 0;
        this.visitNode(node.getBody());
        if (rewritesNo == 0) {
            String msg = "Rules must have at least one rewrite.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }

        if (node.getRequires() != null) {
            inSideCondition = true;
            this.visitNode(node.getRequires());
            inSideCondition = false;
        }
        if (node.getEnsures() != null) {
            inSideCondition = true;
            this.visitNode(node.getEnsures());
            inSideCondition = false;
        }
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _) {
        this.visitNode(node.getBody());
        if (node.getRequires() != null) {
            inSideCondition = true;
            this.visitNode(node.getRequires());
            inSideCondition = false;
        }
        if (node.getEnsures() != null) {
            inSideCondition = true;
            this.visitNode(node.getEnsures());
            inSideCondition = false;
        }
        return null;
    }

    @Override
    public Void visit(TermCons node, Void _) {
        boolean temp = inFunction;
        if (node.getProduction().containsAttribute("function")) {
            //inFunction = true;
        }
        super.visit(node, _);
        inFunction = temp;
        return null;
    }
    
    @Override
    public Void visit(Rewrite node, Void _) {
        if (inConfig) {
            String msg = "Rewrites are not allowed in configurations.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }
        if (inRewrite) {
            String msg = "Rewrites are not allowed to be nested.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }
        if (inSideCondition) {
            String msg = "Rewrites are not allowed in side conditions.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }
        if (inFunction) {
            String msg = "Rewrites are not allowed under functions.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }
        rewritesNo++;
        inRewrite = true;
        super.visit(node, _);
        inRewrite = false;
        return null;
    }
}
