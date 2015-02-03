// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.kil.KItem.KItemOperations;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.Equality.EqualityOperations;
import org.kframework.backend.java.symbolic.SMTOperations;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.utils.inject.RequestScoped;

import com.google.inject.Inject;

@RequestScoped
public class GlobalContext {
    private Definition def;
    public final FileSystem fs;
    public final BuiltinFunction builtins;
    @Deprecated
    public final EqualityOperations equalityOps;
    @Deprecated
    public final SMTOperations constraintOps;
    @Deprecated
    public final KItemOperations kItemOps;

    @Inject
    public GlobalContext(
            FileSystem fs,
            BuiltinFunction builtins,
            EqualityOperations equalityOps,
            SMTOperations constraintOps,
            KItemOperations kItemOps) {
        this.fs = fs;
        this.builtins = builtins;
        this.equalityOps = equalityOps;
        this.constraintOps = constraintOps;
        this.kItemOps = kItemOps;
    }

    public void setDefinition(Definition def) {
        this.def = def;
    }

    public Definition getDefinition() {
        return def;
    }
}