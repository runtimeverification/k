// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.GeneratedSource;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

/**
 *
 * @author YilongL
 */
public class RemovePreincludedRules extends CopyOnWriteTransformer {

    public RemovePreincludedRules(Context context) {
        super("Remove rules that are useless for the Java backend", context);
    }

    @Override
    public ASTNode visit(Rule node, Void _void)  {
        if (node.getSource() instanceof GeneratedSource && ((GeneratedSource)node.getSource()).getSourceClass() == ResolveBinder.class) {
            return null;
        }
        return node;
    }
}
