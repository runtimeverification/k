// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/19/12
 * Time: 3:02 PM
 */
public class AddHeatingConditions extends CopyOnWriteTransformer {
    public AddHeatingConditions(org.kframework.kil.loader.Context context) {
        super("Generate Heating Conditions", context);
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {

        final boolean heating = node.containsAttribute(MetaK.Constants.heatingTag);
        final boolean cooling = node.containsAttribute(MetaK.Constants.coolingTag);
        if (!(heating || cooling))
            return node;
        Term kresultCnd = null;
        if (!(node.getBody() instanceof  Rewrite)) {
            throw KExceptionManager.criticalError(
                            "Heating/Cooling rules should have rewrite at the top.",
                            this, node);
        }
        KSequence kSequence;
        Rewrite rewrite = (Rewrite) node.getBody();
        if (heating) {
            if (!(rewrite.getRight() instanceof KSequence)) {
                throw KExceptionManager.criticalError(
                                "Heating rules should have a K sequence in the rhs.",
                                this, node);
            }
            kSequence = (KSequence) rewrite.getRight();
        } else {
            if (!(rewrite.getLeft() instanceof KSequence)) {
                throw KExceptionManager.criticalError(
                                "Cooling rules should have a K sequence in the lhs.",
                                this, node);
            }
            kSequence = (KSequence) rewrite.getLeft();
        }
        if (kSequence.getContents().size() != 2 ) {
            throw KExceptionManager.criticalError(
                            "Heating/Cooling rules should have exactly 2 items in their K Sequence.",
                                this, node);
        }
        java.util.Set<Variable> vars = kSequence.getContents().get(0).variables();
        if (vars.size() != 1) {
            throw KExceptionManager.criticalError(
                            "Heating/Cooling rules should heat/cool at most one variable.",
                            this, node);
        }
        Variable variable = vars.iterator().next();
        Sort resultType = Sort.of(node.getAttribute("result"));
        KLabel resultLabel = getResultLabel(resultType);
        final KApp isKResult = KApp.of(resultLabel, variable);
        if (heating) {
            kresultCnd = KApp.of(KLabelConstant.KNEQ_KLABEL, isKResult, BoolBuiltin.TRUE);
        } else {
            kresultCnd = isKResult;
        }
        node = node.shallowCopy();
        Term condition = MetaK.incrementCondition(node.getRequires(), kresultCnd);

        node.setRequires(condition);
        return node;
    }

    private KLabel getResultLabel(Sort resultType) {
        if (resultType == null || resultType.getName() == null) {
            return KLabelConstant.KRESULT_PREDICATE;
        }
        if (Character.isUpperCase(resultType.getName().charAt(0))) {
            return KLabelConstant.of(AddPredicates.predicate(resultType));
        }
        return KLabelConstant.of(resultType.getName());


    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }
}
