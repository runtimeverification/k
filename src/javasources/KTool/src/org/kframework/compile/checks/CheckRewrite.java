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
    public void visit(Syntax node) {
    }

    @Override
    public void visit(Configuration node) {
        inConfig = true;
        super.visit(node);
        inConfig = false;
    }

    @Override
    public void visit(Rule node) {
        rewritesNo = 0;
        node.getBody().accept(this);
        if (rewritesNo == 0) {
            String msg = "Rules must have at least one rewrite.";
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER, msg, getName(), node.getFilename(), node.getLocation()));
        }

        if (node.getRequires() != null) {
            inSideCondition = true;
            node.getRequires().accept(this);
            inSideCondition = false;
        }
        if (node.getEnsures() != null) {
            inSideCondition = true;
            node.getEnsures().accept(this);
            inSideCondition = false;
        }
    }

    @Override
    public void visit(org.kframework.kil.Context node) {
        node.getBody().accept(this);
        if (node.getRequires() != null) {
            inSideCondition = true;
            node.getRequires().accept(this);
            inSideCondition = false;
        }
        if (node.getEnsures() != null) {
            inSideCondition = true;
            node.getEnsures().accept(this);
            inSideCondition = false;
        }
    }

    @Override
    public void visit(TermCons node) {
        boolean temp = inFunction;
        if (node.getProduction().containsAttribute("function")) {
            //inFunction = true;
        }
        super.visit(node);
        inFunction = temp;
    }
    
    @Override
    public void visit(Rewrite node) {
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
        super.visit(node);
        inRewrite = false;
    }
}
