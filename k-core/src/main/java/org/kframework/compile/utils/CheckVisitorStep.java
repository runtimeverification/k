// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.loader.Context;

public class CheckVisitorStep<T extends ASTNode> extends BasicCompilerStep<T> implements CheckStep<T> {

    AbstractVisitor<Void, ?, RuntimeException> t;

    public CheckVisitorStep(AbstractVisitor<Void, ?, RuntimeException> t, Context context) {
        super(context);
        this.t = t;
    }

    @Override
    public boolean check(T def) {
        t.visitNode(def);
        if (sw != null) {
            sw.printIntermediate(getName());
        }
        return true;
    }

    @Override
    public String getName() {
        return t.getName();
    }

    @Override
    public T compile(T def, String stepName) {
        check(def);
        return def;
    }
}
