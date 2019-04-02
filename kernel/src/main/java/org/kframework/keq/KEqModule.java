package org.kframework.keq;

import com.google.inject.AbstractModule;
import com.google.inject.Module;
import com.google.inject.Provider;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;
import org.kframework.definition.Definition;
import org.kframework.kompile.BackendModule;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.main.AnnotatedByDefinitionModule;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.rewriter.Rewriter;
import org.kframework.unparser.PrintOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Annotations;
import org.kframework.utils.inject.Main;
import org.kframework.utils.inject.Options;
import org.kframework.utils.inject.Spec1;
import org.kframework.utils.inject.Spec2;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import java.util.List;
import java.util.Map;
import java.util.function.Function;

public class KEqModule extends AbstractModule {
    public static class CommonModule extends AbstractModule {
        @Override
        protected void configure() {
            //bind backend implementations of tools to their interfaces
            install(new BackendModule());

            bind(FileUtil.class);
            bind(FileSystem.class).to(PortableFileSystem.class);
        }

        @Provides
        Function<Definition, Rewriter> getRewriter(KompileOptions options, Map<String, Provider<Function<Definition, Rewriter>>> map, KExceptionManager kem) {
            Provider<Function<Definition, Rewriter>> provider = map.get(options.backend);
            if (provider == null) {
                throw KEMException.criticalError("Backend " + options.backend + " does not support execution. Supported backends are: "
                        + map.keySet());
            }
            return provider.get();
        }
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KEqFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KEQ);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KEqOptions.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
    }

    @Provides
    GlobalOptions globalOptions(KEqOptions options) {
        return options.global;
    }

    @Provides
    SMTOptions smtOptions(KEqOptions options) { return options.smt; }

    @Provides
    PrintOptions printOptions(KEqOptions options) {
        return options.print;
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
        DefinitionLoadingOptions defLoadingOptions(KEqOptions options) {
            return options.definitionLoading;
        }
    }

    public static class Spec1ExecutionContextModule extends AnnotatedByDefinitionModule {

        private final List<Module> definitionSpecificModules;

        public Spec1ExecutionContextModule(List<Module> definitionSpecificModules) {
            this.definitionSpecificModules = definitionSpecificModules;
        }

        @Override
        protected void configure() {
            exposeBindings(definitionSpecificModules, Spec1.class, Annotations::spec1);
        }

        @Provides
        DefinitionLoadingOptions defLoadingOptions(KEqOptions options) {
            return new DefinitionLoadingOptions(options.def1);
        }
    }

    public static class Spec2ExecutionContextModule extends AnnotatedByDefinitionModule {

        private final List<Module> definitionSpecificModules;

        public Spec2ExecutionContextModule(List<Module> definitionSpecificModules) {
            this.definitionSpecificModules = definitionSpecificModules;
        }

        @Override
        protected void configure() {
            exposeBindings(definitionSpecificModules, Spec2.class, Annotations::spec2);
        }

        @Provides
        DefinitionLoadingOptions defLoadingOptions(KEqOptions options) {
            return new DefinitionLoadingOptions(options.def2);
        }
    }
}


