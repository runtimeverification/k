// Copyright (c) 2014-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.kil.KItem.KItemOperations;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.SymbolicConstraint.EqualityOperations;
import org.kframework.krun.api.io.FileSystem;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class GlobalContext {
    private Definition def;
    public final FileSystem fs;
    public final BuiltinFunction builtins;
    public final EqualityOperations equalityOps;
    public final KItemOperations kItemOps;

    @Inject
    public GlobalContext(
            FileSystem fs,
            BuiltinFunction builtins,
            EqualityOperations equalityOps,
            KItemOperations kItemOps) {
        this.fs = fs;
        this.builtins = builtins;
        this.equalityOps = equalityOps;
        this.kItemOps = kItemOps;
    }

    public void setDefinition(Definition def) {
        this.def = def;
    }

    public Definition getDefinition() {
        return def;
    }
}