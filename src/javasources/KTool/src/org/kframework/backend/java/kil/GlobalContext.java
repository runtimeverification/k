// Copyright (c) 2014-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.krun.api.io.FileSystem;

public class GlobalContext {
    public final Definition def;
    public final FileSystem fs;
    public final BuiltinFunction builtins;
    public GlobalContext(Definition def, FileSystem fs) {
        this.def = def;
        this.fs = fs;
        this.builtins = new BuiltinFunction(def);
    }
}