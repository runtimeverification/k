// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.kil.KItem.KItemOperations;
import org.kframework.backend.java.symbolic.Equality.EqualityOperations;
import org.kframework.backend.java.symbolic.SMTOperations;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.main.Tool;

import com.google.inject.Inject;
import com.google.inject.Singleton;

import java.io.Serializable;

@Singleton
public class GlobalContext implements Serializable {
    private Definition def;
    public final transient FileSystem fs;
    public final transient Tool tool;
    @Deprecated
    public final transient EqualityOperations equalityOps;
    @Deprecated
    public final transient SMTOperations constraintOps;
    @Deprecated
    public final transient KItemOperations kItemOps;

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
