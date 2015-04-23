// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.backend.java.kil.KItem.KItemOperations;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.Equality.EqualityOperations;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.SMTOperations;
import org.kframework.backend.java.symbolic.Stage;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Builtins;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.SMTOptions;

import java.io.Serializable;
import java.lang.invoke.MethodHandle;
import java.util.Map;

@RequestScoped
public class GlobalContext implements Serializable {
    private Definition def;
    public final transient FileSystem fs;
    public final Stage stage;
    public final transient EqualityOperations equalityOps;
    public final transient SMTOperations constraintOps;
    public final transient KItemOperations kItemOps;
    public final KRunOptions krunOptions;
    public final GlobalOptions globalOptions;

    @Inject
    public GlobalContext(
            FileSystem fs,
            JavaExecutionOptions javaOptions,
            GlobalOptions globalOptions,
            KRunOptions krunOptions,
            KExceptionManager kem,
            SMTOptions smtOptions,
            @Builtins Map<String, Provider<MethodHandle>> hookProvider,
            FileUtil files,
            Stage stage) {
        this.fs = fs;
        this.globalOptions = globalOptions;
        this.krunOptions = krunOptions;
        this.equalityOps = new EqualityOperations(() -> def, javaOptions);
        this.constraintOps = new SMTOperations(() -> def, smtOptions, new Z3Wrapper(smtOptions, kem, globalOptions, files));
        this.kItemOps = new KItemOperations(stage, javaOptions, kem, () -> new BuiltinFunction(def, hookProvider, kem, stage), globalOptions);
        this.stage = stage;
    }

    public void setDefinition(Definition def) {
        this.def = def;
    }

    public Definition getDefinition() {
        return def;
    }
}
