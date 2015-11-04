// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import com.beust.jcommander.JCommander;
import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import com.google.inject.name.Named;
import com.google.inject.throwingproviders.ThrowingProviderBinder;
import org.kframework.unparser.OutputModes;
import org.kframework.kil.Configuration;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.krun.modes.DebugMode.DebugExecutionMode;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.krun.modes.KRunExecutionMode;
import org.kframework.main.AnnotatedByDefinitionModule;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Annotations;
import org.kframework.utils.inject.DefinitionScoped;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import java.util.List;
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
    ColorOptions colorOptions(KRunOptions options) {
        return options.color;
    }

    @Provides
    OutputModes outputModes(KRunOptions options) {
        return options.output;
    }

    public static class CommonModule extends AbstractModule {

        @Override
        protected void configure() {
            //bind backend implementations of tools to their interfaces
            MapBinder<String, Function<org.kframework.definition.Module, Rewriter>> rewriterBinder = MapBinder.newMapBinder(
                    binder(), TypeLiteral.get(String.class), new TypeLiteral<Function<org.kframework.definition.Module, Rewriter>>() {
                    });

            //TODO(cos): move to tiny module
            rewriterBinder.addBinding("tiny").toInstance(m -> new org.kframework.tiny.FullTinyRewriter(m));

            bind(FileUtil.class);

            bind(FileSystem.class).to(PortableFileSystem.class);

            MapBinder<ToolActivation, ExecutionMode> executionBinder = MapBinder.newMapBinder(binder(),
                    ToolActivation.class, ExecutionMode.class);

            executionBinder.addBinding(new ToolActivation.OptionActivation("--debugger")).to(DebugExecutionMode.class);

        }

        @Provides
        DefinitionLoadingOptions defLoadingOptions(ConfigurationCreationOptions options) {
            return options.definitionLoading;
        }

        @Provides
        Function<org.kframework.definition.Module, Rewriter> getRewriter(KompileOptions options, Map<String, Provider<Function<org.kframework.definition.Module, Rewriter>>> map, KExceptionManager kem) {
            Provider<Function<org.kframework.definition.Module, Rewriter>> provider = map.get(options.backend);
            if (provider == null) {
                throw KEMException.criticalError("Backend " + options.backend + " does not support execution. Supported backends are: "
                        + map.keySet());
            }
            return provider.get();
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

        @Provides @DefinitionScoped
        Configuration configuration(BinaryLoader loader, Context context, Stopwatch sw, FileUtil files) {
            Configuration cfg = loader.loadOrDie(Configuration.class,
                    files.resolveKompiled("configuration.bin"));
            sw.printIntermediate("Reading configuration from binary");
            return cfg;
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

    public static class MainExecutionContextModule extends AnnotatedByDefinitionModule {

        private final List<Module> definitionSpecificModules;

        public MainExecutionContextModule(List<Module> definitionSpecificModules) {
            this.definitionSpecificModules = definitionSpecificModules;
        }

        @Override
        protected void configure() {
            exposeBindings(definitionSpecificModules, Main.class, Annotations::main);
        }

        @Provides
        ConfigurationCreationOptions ccOptions(KRunOptions options) {
            return options.configurationCreation;
        }
    }
}
