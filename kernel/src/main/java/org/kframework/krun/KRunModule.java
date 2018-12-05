// Copyright (c) 2014-2018 K Team. All Rights Reserved.
package org.kframework.krun;

import com.beust.jcommander.JCommander;
import com.google.inject.AbstractModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import com.google.inject.name.Named;
import com.google.inject.throwingproviders.ThrowingProviderBinder;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.krun.modes.DebugMode.DebugExecutionMode;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.krun.modes.KRunExecutionMode;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.OutputModes;
import org.kframework.unparser.PrintOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Options;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import java.util.Map;
import java.util.function.Function;

public class KRunModule extends AbstractModule {

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KRunFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KRUN);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KRunOptions.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(KRunOptions.Experimental.class);
        experimentalOptionsBinder.addBinding().toInstance(SMTOptions.class);

        ThrowingProviderBinder throwingBinder = ThrowingProviderBinder.create(binder());
    }

    @Provides
    SMTOptions smtOptions(KRunOptions options) {
        return options.experimental.smt;
    }

    @Provides
    GlobalOptions globalOptions(KRunOptions options) {
        return options.global;
    }

    @Provides
    PrintOptions printOptions(KRunOptions options) {
        return options.print;
    }

    @Provides
    OutputModes outputModes(PrintOptions options) {
        return options.output;
    }

    public static class CommonModule extends AbstractModule {

        @Override
        protected void configure() {
            install(new RewriterModule());

            //bind backend implementations of tools to their interfaces
            MapBinder<ToolActivation, ExecutionMode> executionBinder = MapBinder.newMapBinder(binder(),
                    ToolActivation.class, ExecutionMode.class);

            executionBinder.addBinding(new ToolActivation.OptionActivation("--debugger")).to(DebugExecutionMode.class);

        }

        @Provides
        DefinitionLoadingOptions defLoadingOptions(ConfigurationCreationOptions options) {
            return options.definitionLoading;
        }

        @Provides
        ConfigurationCreationOptions ccOptions(KRunOptions options) {
            return options.configurationCreation;
        }

        @Provides
        ExecutionMode getExecutionMode(JCommander jc, Map<ToolActivation, Provider<ExecutionMode>> map, KRunOptions kRunOptions, KExceptionManager kem, FileUtil files) {
            ExecutionMode res = null;
            ToolActivation previous = null;
            for (Map.Entry<ToolActivation, Provider<ExecutionMode>> entry : map.entrySet()) {
                if (entry.getKey().isActive(jc)) {
                    if (res != null) {
                        throw KEMException.criticalError("Multiple tool activations found: " + entry.getKey() + " and " + previous);
                    }
                    res = entry.getValue().get();
                    previous = entry.getKey();
                }
            }
            if (res == null)
                res = new KRunExecutionMode(kRunOptions, kem, files);
            return res;
        }


        @Provides
        @Named("checkpointIntervalValue")
        Integer getCheckpointLength(KompileOptions options, @Named("checkpointIntervalMap") Map<String, Integer> map) {
            Integer checkpointInterval = map.get(options.backend);
            if (checkpointInterval == null) {
                return new Integer(50);
            }
            return checkpointInterval;
        }
    }
}
