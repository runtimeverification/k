// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.lang.reflect.Field;
import java.util.List;
import java.util.Map;

import org.kframework.backend.unparser.BinaryOutputMode;
import org.kframework.backend.unparser.KASTOutputMode;
import org.kframework.backend.unparser.NoOutputMode;
import org.kframework.backend.unparser.OutputModes;
import org.kframework.backend.unparser.PrettyPrintingOutputMode;
import org.kframework.backend.unparser.PrintKRunGraph;
import org.kframework.backend.unparser.PrintKRunResult;
import org.kframework.backend.unparser.PrintSearchResult;
import org.kframework.backend.unparser.PrintSearchResults;
import org.kframework.backend.unparser.PrintTerm;
import org.kframework.backend.unparser.PrintTransition;
import org.kframework.backend.unparser.RawOutputMode;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.InitialConfigurationProvider;
import org.kframework.krun.KRunOptions.ConfigurationCreationOptions;
import org.kframework.krun.api.ExecutorDebugger;
import org.kframework.krun.api.KRunGraph;
import org.kframework.krun.api.KRunResult;
import org.kframework.krun.api.KRunState;
import org.kframework.krun.api.SearchResult;
import org.kframework.krun.api.SearchResults;
import org.kframework.krun.api.Transition;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.krun.tools.Debugger;
import org.kframework.krun.tools.Executor;
import org.kframework.krun.tools.LtlModelChecker;
import org.kframework.krun.tools.Prover;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.transformation.ActivatedTransformationProvider;
import org.kframework.transformation.BasicTransformationProvider;
import org.kframework.transformation.ToolActivation;
import org.kframework.transformation.Transformation;
import org.kframework.transformation.TransformationCompositionProvider;
import org.kframework.transformation.TransformationMembersInjector;
import org.kframework.transformation.TransformationProvider;
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.InjectGeneric;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import com.google.common.reflect.TypeParameter;
import com.google.common.reflect.TypeToken;
import com.google.inject.AbstractModule;
import com.google.inject.Binding;
import com.google.inject.Key;
import com.google.inject.Module;
import com.google.inject.PrivateModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.Singleton;
import com.google.inject.TypeLiteral;
import com.google.inject.matcher.Matchers;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;
import com.google.inject.spi.DefaultElementVisitor;
import com.google.inject.spi.Element;
import com.google.inject.spi.Elements;
import com.google.inject.spi.TypeEncounter;
import com.google.inject.spi.TypeListener;
import com.google.inject.throwingproviders.ThrowingProviderBinder;

public class KRunModule extends AbstractModule {

    private final KRunOptions options;

    public KRunModule(KRunOptions options) {
        this.options = options;
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KRunFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KRUN);
        bind(KRunOptions.class).toInstance(options);
        bind(SMTOptions.class).toInstance(options.experimental.smt);
        bind(GlobalOptions.class).toInstance(options.global);
        bind(ColorOptions.class).toInstance(options.color);

        bind(FileSystem.class).to(PortableFileSystem.class);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().toInstance(options);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(KRunOptions.Experimental.class);
        experimentalOptionsBinder.addBinding().toInstance(SMTOptions.class);

        bind(OutputModes.class).toInstance(options.output);

        ThrowingProviderBinder throwingBinder = ThrowingProviderBinder.create(binder());

        // bind Transformation<P, Q> to TransformationProvider<Transformation<P, Q>>
        bindListener(Matchers.any(), new TypeListener() {

            @Override
            public <I> void hear(TypeLiteral<I> typeLiteral, TypeEncounter<I> typeEncounter) {
                for (Field field : typeLiteral.getRawType().getDeclaredFields()) {
                    if (field.getType() == Transformation.class && field.isAnnotationPresent(InjectGeneric.class)) {
                      TypeToken<?> fieldType = TypeToken.of(typeLiteral.getFieldType(field).getType());
                      TypeToken<? extends TransformationProvider<?>> genericProviderTypeToken = providerOf(fieldType);
                      TypeLiteral<? extends TransformationProvider<?>> genericProviderTypeLiteral = (TypeLiteral<? extends TransformationProvider<?>>) TypeLiteral.get(genericProviderTypeToken.getType());
                      typeEncounter.register(new TransformationMembersInjector<I>(field, typeEncounter.getProvider(Key.get(genericProviderTypeLiteral))));
                    }
                }
            }

            private <T> TypeToken<TransformationProvider<T>> providerOf(TypeToken<T> transformationType) {
                return new TypeToken<TransformationProvider<T>>() {}.where(new TypeParameter<T>() {}, transformationType);
            }
        });

        // bind providers for atomic transformations activated by options
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<ASTNode, String>>() {}).to(Key.get(new TypeLiteral<ActivatedTransformationProvider<ASTNode, String>>() {}));
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<KRunState, ASTNode>>() {}).to(Key.get(new TypeLiteral<ActivatedTransformationProvider<KRunState, ASTNode>>() {}));
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<SearchResult, Map<String, Term>>>() {}).to(Key.get(new TypeLiteral<ActivatedTransformationProvider<SearchResult, Map<String, Term>>>() {}));
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<KRunResult<?>, String>>() {}).to(Key.get(new TypeLiteral<ActivatedTransformationProvider<KRunResult<?>, String>>() {}));
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<Void, KRunResult<?>>>() {}).to(Key.get(new TypeLiteral<ActivatedTransformationProvider<Void, KRunResult<?>>>() {}));

        // bind providers for transformations that are on universally
        bind(new TypeLiteral<TransformationProvider<Transformation<Transition, String>>>() {}).to(new TypeLiteral<BasicTransformationProvider<Transformation<Transition, String>, PrintTransition>>() {});
        bind(new TypeLiteral<TransformationProvider<Transformation<SearchResults, String>>>() {}).to(new TypeLiteral<BasicTransformationProvider<Transformation<SearchResults, String>, PrintSearchResults>>() {});
        bind(new TypeLiteral<TransformationProvider<Transformation<Map<String, Term>, String>>>() {}).to(new TypeLiteral<BasicTransformationProvider<Transformation<Map<String, Term>, String>, PrintSearchResult>>() {});
        bind(new TypeLiteral<TransformationProvider<Transformation<KRunGraph, String>>>() {}).to(new TypeLiteral<BasicTransformationProvider<Transformation<KRunGraph, String>, PrintKRunGraph>>() {});
        bind(new TypeLiteral<TransformationProvider<Transformation<String, Void>>>() {}).to(new TypeLiteral<BasicTransformationProvider<Transformation<String, Void>, WriteOutput>>() {});

        // bind providers for transformatinos composed of smaller transformations
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<Void, Void>>() {}).to(Key.get(new TypeLiteral<TransformationCompositionProvider<Void, KRunResult<?>, Void>>() {}));
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<KRunState, String>>() {}).to(Key.get(new TypeLiteral<TransformationCompositionProvider<KRunState, ASTNode, String>>() {}));
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<SearchResult, String>>() {}).to(Key.get(new TypeLiteral<TransformationCompositionProvider<SearchResult, Map<String, Term>, String>>() {}));
        throwingBinder.bind(TransformationProvider.class, new TypeLiteral<Transformation<KRunResult<?>, Void>>() {}).to(Key.get(new TypeLiteral<TransformationCompositionProvider<KRunResult<?>, String, Void>>() {}));

        //bind option activations to the transformations they activate
        MapBinder<ToolActivation, Transformation<Void, Void>> mainTools = MapBinder.newMapBinder(
                binder(), TypeLiteral.get(ToolActivation.class), new TypeLiteral<Transformation<Void, Void>>() {});
        MapBinder<ToolActivation, Transformation<Void, KRunResult<?>>> krunResultTools = MapBinder.newMapBinder(
                binder(), TypeLiteral.get(ToolActivation.class), new TypeLiteral<Transformation<Void, KRunResult<?>>>() {});
        mainTools.addBinding(new ToolActivation.OptionActivation("--debugger")).to(Debugger.Tool.class);
        krunResultTools.addBinding(new ToolActivation.OptionActivation("--ltlmc")).to(LtlModelChecker.Tool.class);
        krunResultTools.addBinding(new ToolActivation.OptionActivation("--ltlmc-file")).to(LtlModelChecker.Tool.class);
        krunResultTools.addBinding(new ToolActivation.OptionActivation("--prove")).to(Prover.Tool.class);

        MapBinder<ToolActivation, Transformation<KRunResult<?>, String>> krunResultPrinters = MapBinder.newMapBinder(
                binder(), TypeLiteral.get(ToolActivation.class), new TypeLiteral<Transformation<KRunResult<?>, String>>() {});
        MapBinder<ToolActivation, Transformation<ASTNode, String>> astNodePrinters = MapBinder.newMapBinder(
                binder(), TypeLiteral.get(ToolActivation.class), new TypeLiteral<Transformation<ASTNode, String>>() {});
        MapBinder<ToolActivation, Transformation<KRunState, ASTNode>> krunStatePrinters = MapBinder.newMapBinder(
                binder(), TypeLiteral.get(ToolActivation.class), new TypeLiteral<Transformation<KRunState, ASTNode>>() {});
        MapBinder<ToolActivation, Transformation<SearchResult, Map<String, Term>>> searchResultPrinters = MapBinder.newMapBinder(
                binder(), TypeLiteral.get(ToolActivation.class), new TypeLiteral<Transformation<SearchResult, Map<String, Term>>>() {});
        krunResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.BINARY)).to(BinaryOutputMode.class);
        krunResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.NONE)).to(NoOutputMode.class);
        krunResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.RAW)).to(RawOutputMode.PrintKRunResult.class);
        krunStatePrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.RAW)).to(KASTOutputMode.PrintKRunState.class);
        astNodePrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.RAW)).to(RawOutputMode.PrintASTNode.class);
        searchResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.RAW)).to(KASTOutputMode.PrintSearchResult.class);
        krunResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.KAST)).to(PrintKRunResult.class);
        krunStatePrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.KAST)).to(KASTOutputMode.PrintKRunState.class);
        astNodePrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.KAST)).to(PrintTerm.class);
        searchResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", OutputModes.KAST)).to(KASTOutputMode.PrintSearchResult.class);
        for (OutputModes mode : OutputModes.values()) {
            if (mode.isPrettyPrinting()) {
                krunResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", mode)).to(PrintKRunResult.class);
                krunStatePrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", mode)).to(PrettyPrintingOutputMode.PrintKRunState.class);
                searchResultPrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", mode)).to(PrettyPrintingOutputMode.PrintSearchResult.class);
                astNodePrinters.addBinding(new ToolActivation.OptionValueActivation<>("--output", mode)).to(PrintTerm.class);
            }
        }
    }

    public static class CommonModule extends AbstractModule {

        @Override
        protected void configure() {
            //bind backend implementations of tools to their interfaces
            MapBinder.newMapBinder(
                    binder(), String.class, Executor.class);

            MapBinder.newMapBinder(
                    binder(), String.class, LtlModelChecker.class);

            MapBinder.newMapBinder(
                    binder(), String.class, Prover.class);

            bind(Debugger.class).to(ExecutorDebugger.class);

            bind(Term.class).toProvider(InitialConfigurationProvider.class);

            bind(FileUtil.class);

        }

        @Provides
        DefinitionLoadingOptions defLoadingOptions(ConfigurationCreationOptions options) {
            return options.definitionLoading;
        }

        @Provides
        Executor getExecutor(KompileOptions options, Map<String, Provider<Executor>> map, KExceptionManager kem) {
            Provider<Executor> provider = map.get(options.backend);
            if (provider == null) {
                throw KExceptionManager.criticalError("Backend " + options.backend + " does not support execution. Supported backends are: "
                        + map.keySet());
            }
            return provider.get();
        }

        @Provides
        LtlModelChecker getModelChecker(KompileOptions options, Map<String, Provider<LtlModelChecker>> map, KExceptionManager kem) {
            Provider<LtlModelChecker> provider = map.get(options.backend);
            if (provider == null) {
                throw KExceptionManager.criticalError("Backend " + options.backend + " does not support ltl model checking. Supported backends are: "
                        + map.keySet());
            }
            return provider.get();
        }

        @Provides
        Prover getProver(KompileOptions options, Map<String, Provider<Prover>> map, KExceptionManager kem) {
            Provider<Prover> provider = map.get(options.backend);
            if (provider == null) {
                throw KExceptionManager.criticalError("Backend " + options.backend + " does not support program verification. Supported backends are: "
                        + map.keySet());
            }
            return provider.get();
        }

        @Provides @Singleton
        Configuration configuration(BinaryLoader loader, Context context, Stopwatch sw, FileUtil files) {
            Configuration cfg = loader.loadOrDie(Configuration.class,
                    files.resolveKompiled("configuration.bin"));
            sw.printIntermediate("Reading configuration from binary");
            return cfg;
        }
    }

    public static class MainExecutionContextModule extends PrivateModule {

        private final KRunOptions options;
        private final List<Module> definitionSpecificModules;

        public MainExecutionContextModule(KRunOptions options, List<Module> definitionSpecificModules) {
            this.options = options;
            this.definitionSpecificModules = definitionSpecificModules;
        }

        @Override
        protected void configure() {
            for (Element element : Elements.getElements(definitionSpecificModules)) {
                element.acceptVisitor(new DefaultElementVisitor<Void>() {
                    @Override
                    public <T> Void visit(Binding<T> binding) {
                        Key<T> key = binding.getKey();
                        if (key.getAnnotation() == null && key.getAnnotationType() == null) {
                            bind(key.getTypeLiteral()).annotatedWith(Main.class).to(key.getTypeLiteral());
                            expose(key.getTypeLiteral()).annotatedWith(Main.class);
                        }
                        return null;
                    }
                });
            }
            for (Module m : definitionSpecificModules) {
                install(m);
            }

            bind(ConfigurationCreationOptions.class).toInstance(options.configurationCreation);
        }
    }
}
