// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.AbstractTransformer;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;


public class CompilerTransformerStep<T extends ASTNode> extends BasicCompilerStep<T> {

    AbstractTransformer<RuntimeException> t;

    public CompilerTransformerStep(AbstractTransformer<RuntimeException> t, Context context) {
        super(context);
        this.t = t;
    }

    @Override
    public T compile(T def, String stepName) {
        ASTNode result = null;
        result = t.visitNode(def);
        if (!def.getClass().isInstance(result)) {
            GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
                    KException.KExceptionGroup.INTERNAL,
                    "Expecting " + def.getClass().getName() + ", but got " + result.getClass().getName()
                    + " while applying" + getName() + ".",
                    def.getFilename(), def.getLocation()));
        }
        // we checked above that result is an instance of the class of def.
        @SuppressWarnings("unchecked")
        T resultT = (T) result;
        if (sw != null) {
            sw.printIntermediate(getName());
        }
        return resultT;
    }

    @Override
    public String getName() {
        return t.getName();
    }
}
