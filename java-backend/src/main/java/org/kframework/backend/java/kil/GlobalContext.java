// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.kil.KItem.KItemOperations;
import org.kframework.backend.java.symbolic.Equality.EqualityOperations;
import org.kframework.backend.java.symbolic.SMTOperations;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.main.Tool;

import com.google.inject.Inject;
import com.google.inject.Singleton;

@Singleton
public class GlobalContext {
    private Definition def;
    public final FileSystem fs;
    public final Tool tool;
    @Deprecated
    public final EqualityOperations equalityOps;
    @Deprecated
    public final SMTOperations constraintOps;
    @Deprecated
    public final KItemOperations kItemOps;

    @Inject
    public GlobalContext(
            FileSystem fs,
            EqualityOperations equalityOps,
            SMTOperations constraintOps,
            KItemOperations kItemOps,
            Tool tool) {
        this.fs = fs;
        this.equalityOps = equalityOps;
        this.constraintOps = constraintOps;
        this.kItemOps = kItemOps;
        this.tool = tool;
    }

    public void setDefinition(Definition def) {
        this.def = def;
    }

    public Definition getDefinition() {
        return def;
    }
}
