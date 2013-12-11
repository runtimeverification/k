package org.kframework.backend.java.symbolic;

import java.util.HashSet;
import java.util.Set;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Constants;

/**
 * Checks syntactic constructs tagged with label [left] are actually
 * left-associative.
 * 
 * @author YilongL
 * 
 */
public class CheckingLeftAssocConstructs implements KastStructureCheckerPlugin {

    private final Set<KLabelConstant> leftAssocKLabels = new HashSet<KLabelConstant>();

    private final LocalVisitor preVisitor = new CheckLeftAssociativity();
    private final LocalVisitor postVisitor = null;
    private PluggableKastStructureChecker checker;
    
    public CheckingLeftAssocConstructs(Definition definition) {
        for (KLabel kLabel : definition.kLabels()) {
            if (kLabel instanceof KLabelConstant) {
                if (((KLabelConstant) kLabel).productions().size() != 1) {
                    // TODO(YilongL): is it possible that one of the production
                    // has attribute [left]?
                    continue;
                }
                
                Production prod = ((KLabelConstant) kLabel).productions().get(0);
                if (prod.containsAttribute(Constants.LEFT)) {
                    leftAssocKLabels.add((KLabelConstant) kLabel);
                }
            }
        }
    }

    @Override
    public void registerTo(PluggableKastStructureChecker checker) {
        assert this.checker == null;
        this.checker = checker;
    }        
    
    @Override
    public void reset() {
        preVisitor.resetProceed();
    }
    
    @Override
    public LocalVisitor getPreVisitor() {
        return preVisitor;
    }

    @Override
    public LocalVisitor getPostVisitor() {
        return postVisitor;
    }

    private class CheckLeftAssociativity extends LocalVisitor {
        @Override
        public void visit(KItem kItem) {
            KLabel kLabel1 = kItem.kLabel();
            if (leftAssocKLabels.contains(kLabel1)) {
                if (kItem.kList().size() != 2) {
                    // TODO(YilongL): why is 'notBool or absInt left-assoc?
                    return;
                }
                
                if (kItem.kList().get(1) instanceof KItem) {
                    KLabel kLabel2 = ((KItem) kItem.kList().get(1)).kLabel();
                    
                    if (kLabel1.equals(kLabel2)) {
                        this.proceed = false;
                        checker.flagFailure(CheckingLeftAssocConstructs.this);
                        return;
                    }
                }
            }
        }
    }
}
