// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.loader.Context;
import org.kframework.krun.ColorOptions;
import org.kframework.transformation.Transformation;

import com.google.inject.Inject;

public class PrintTerm implements Transformation<ASTNode, String> {

    private final ColorOptions colorOptions;
    private final OutputModes mode;

    @Inject
    public PrintTerm(
            ColorOptions colorOptions,
            OutputModes mode) {
        this.colorOptions = colorOptions;
        this.mode = mode;
    }

    @Override
    public String run(ASTNode node, Attributes a) {
        UnparserFilter printer = new UnparserFilter(true,colorOptions.color(),
                mode, false, a.typeSafeGet(Context.class));
        printer.visitNode(node);
        return printer.getResult();
    }

    @Override
    public String getName() {
        return "print term";
    }

}
