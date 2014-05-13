// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;
import java.util.List;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/19/12
 * Time: 3:02 PM
 */
public class FreezeUserFreezers extends CopyOnWriteTransformer {
    public FreezeUserFreezers(Context context) {
        super("Freeze User Freezers", context);
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
        if (!(node.getBody() instanceof  Rewrite)) {
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.CRITICAL,
                            "Heating/Cooling rules should have rewrite at the top.",
                            getName(),
                            node.getFilename(),
                            node.getLocation())
            );
        }
        KSequence kSequence;
        Rewrite rewrite = (Rewrite) node.getBody();
        if (heating) {
            if (!(rewrite.getRight() instanceof KSequence)) {
                GlobalSettings.kem.register(
                        new KException(KException.ExceptionType.ERROR,
                                KException.KExceptionGroup.CRITICAL,
                                "Heating rules should have a K sequence in the rhs.",
                                getName(),
                                node.getFilename(),
                                node.getLocation())
                );
            }
            kSequence = (KSequence) rewrite.getRight();
        } else {
            if (!(rewrite.getLeft() instanceof KSequence)) {
                GlobalSettings.kem.register(
                        new KException(KException.ExceptionType.ERROR,
                                KException.KExceptionGroup.CRITICAL,
                                "Cooling rules should have a K sequence in the lhs.",
                                getName(),
                                node.getFilename(),
                                node.getLocation())
                );
            }
            kSequence = (KSequence) rewrite.getLeft();
        }
        List<Term> kSequenceContents = kSequence.getContents();
        if (kSequenceContents.size() != 2 ) {
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.CRITICAL,
                            "Heating/Cooling rules should have exactly 2 items in their K Sequence.",
                                getName(),
                                node.getFilename(),
                                node.getLocation())
                );
        }
        final Term freezer = kSequenceContents.get(1);
        if (!(freezer instanceof  Freezer)) {
            kSequenceContents = new ArrayList<Term>(kSequenceContents);
            kSequenceContents.set(1, new ContextsToHeating(context).freeze(freezer));
            kSequence = kSequence.shallowCopy();
            kSequence.setContents(kSequenceContents);
            rewrite = rewrite.shallowCopy();
            if (heating) {
                rewrite.replaceChildren(rewrite.getLeft(), kSequence, context);
            } else {
                rewrite.replaceChildren(kSequence, rewrite.getRight(), context);
            }
            node = node.shallowCopy();
            node.setBody(rewrite);
        }
        return node;
    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }
}
