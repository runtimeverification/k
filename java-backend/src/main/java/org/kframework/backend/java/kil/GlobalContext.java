// Copyright (c) 2014-2019 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import org.kframework.backend.java.kil.KItem.KItemOperations;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.Equality.EqualityOperations;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.SMTOperations;
import org.kframework.backend.java.symbolic.Stage;
import org.kframework.backend.java.util.FormulaSimplificationCache;
import org.kframework.backend.java.util.PrettyPrinter;
import org.kframework.backend.java.util.Profiler2;
import org.kframework.backend.java.util.StateLog;
import org.kframework.backend.java.util.ToStringCache;
import org.kframework.backend.java.util.Z3Wrapper;
import org.kframework.kprove.KProveOptions;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.unparser.KPrint;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.SMTOptions;

import java.io.IOException;
import java.io.Serializable;
import java.lang.invoke.MethodHandle;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.Formatter;
import java.util.Map;

public class GlobalContext implements Serializable {
    private Definition def;
    public final transient FileSystem fs;
    public final Stage stage;
    public final transient EqualityOperations equalityOps;
    public final transient SMTOperations constraintOps;
    public final transient KItemOperations kItemOps;
    public final transient KRunOptions krunOptions;
    public final transient KProveOptions kproveOptions;
    public final transient JavaExecutionOptions javaExecutionOptions;
    public final transient KExceptionManager kem;
    private final transient Map<String, MethodHandle> hookProvider;
    public final transient FileUtil files;
    public final transient GlobalOptions globalOptions;
    public final transient Profiler2 profiler;
    public final StateLog stateLog;
    public final PrettyPrinter prettyPrinter;
    public final transient FunctionCache functionCache = new FunctionCache();
    public final transient FormulaSimplificationCache formulaCache = new FormulaSimplificationCache();
    public final transient ToStringCache toStringCache = new ToStringCache();

    private boolean isExecutionPhase = true;

    private transient Formatter log = new Formatter(System.err);
    private transient Deque<Formatter> logStack = new ArrayDeque<>();

    public GlobalContext(
            FileSystem fs,
            GlobalOptions globalOptions,
            KRunOptions krunOptions,
            KProveOptions kproveOptions,
            JavaExecutionOptions javaExecutionOptions,
            KExceptionManager kem,
            SMTOptions smtOptions,
            Map<String, MethodHandle> hookProvider,
            FileUtil files,
            Stage stage,
            Profiler2 profiler,
            KPrint kprint,
            org.kframework.definition.Definition coreDefinition) {
        this.fs = fs;
        this.globalOptions = globalOptions;
        this.krunOptions = krunOptions;
        this.kproveOptions = kproveOptions;
        this.javaExecutionOptions = javaExecutionOptions;
        this.kem = kem;
        this.hookProvider = hookProvider;
        this.files = files;
        this.equalityOps = new EqualityOperations(() -> def);
        prettyPrinter = new PrettyPrinter(kprint, coreDefinition);
        this.stateLog = new StateLog(javaExecutionOptions, files, prettyPrinter);
        this.constraintOps = new SMTOperations(() -> def, smtOptions,
                new Z3Wrapper(smtOptions, kem, javaExecutionOptions, files, stateLog, this), kem, javaExecutionOptions);
        this.kItemOps = new KItemOperations(stage, javaExecutionOptions.deterministicFunctions, kem, this::builtins, globalOptions);
        this.stage = stage;
        this.profiler = profiler;

    }

    private transient BuiltinFunction builtinFunction;
    private BuiltinFunction builtins() {
        BuiltinFunction b = builtinFunction;
        if (b == null) {
            b = new BuiltinFunction(def, hookProvider, kem, stage);
            builtinFunction = b;
        }
        return b;
    }

    public void setDefinition(Definition def) {
        this.def = def;
    }

    public Definition getDefinition() {
        return def;
    }

    public boolean isExecutionPhase() {
        return isExecutionPhase;
    }

    public void setExecutionPhase(boolean executionPhase) {
        isExecutionPhase = executionPhase;
        if (!executionPhase) {
            profiler.logParsingTime(this);
            javaExecutionOptions.logRulesPublic = javaExecutionOptions.logRulesInit;
            javaExecutionOptions.logFunctionTargetPublic = false;
        } else {
            profiler.logInitTime(this);
            javaExecutionOptions.logRulesPublic = javaExecutionOptions.logRules;
            javaExecutionOptions.logFunctionTargetPublic = javaExecutionOptions.logFunctionTarget;
        }
    }

    public Formatter log() {
        return log;
    }

    public void openLogWrapper() {
        logStack.push(log);
        log = new Formatter(new StringBuilder());
    }

    /**
     * Flush the last log wrapper into the parent log, with all lines indented by {@code indent}.
     */
    public void flushLogWrapper(String indent) {
        StringBuilder sb = (StringBuilder) log.out();
        StringUtil.replaceAll(sb, "\n", "\n" + indent, false);
        log = logStack.pop();
        try {
            log.out().append(sb);
        } catch (IOException e) {
            throw KEMException.criticalError(e.getMessage(), e);
        }
    }
}
