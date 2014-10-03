// Copyright (c) 2014-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.kil.KItem.KItemOperations;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.SymbolicConstraint.SymbolicConstraintOperations;
import org.kframework.krun.api.io.FileSystem;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class GlobalContext {
    private Definition def;
    public final FileSystem fs;
    public final BuiltinFunction builtins;
    public final SymbolicConstraintOperations constraintOps;
    public final KItemOperations kItemOps;

    @Inject
    public GlobalContext(
            FileSystem fs,
            BuiltinFunction builtins,
            SymbolicConstraintOperations equalityOps,
            KItemOperations kItemOps) {
        this.fs = fs;
        this.builtins = builtins;
        this.constraintOps = equalityOps;
        this.kItemOps = kItemOps;
    }

    public void setDefinition(Definition def) {
        this.def = def;
    }

    public Definition getDefinition() {
        return def;
    }
}