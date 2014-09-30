// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import java.util.Map;

import org.kframework.backend.Backend;
import org.kframework.backend.Backends;
import org.kframework.backend.coq.CoqBackend;
import org.kframework.backend.html.HtmlBackend;
import org.kframework.backend.latex.DocumentationBackend;
import org.kframework.backend.latex.LatexBackend;
import org.kframework.backend.latex.PdfBackend;
import org.kframework.backend.maude.KompileBackend;
import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.backend.unparser.UnflattenBackend;
import org.kframework.backend.unparser.UnparserBackend;
import org.kframework.kil.loader.Context;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.inject.Options;
import org.kframework.utils.options.SMTOptions;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.MapBinder;
import com.google.inject.multibindings.Multibinder;

public class KompileModule extends AbstractModule {

    private final Context context;
    private final KompileOptions options;

    public KompileModule(Context context, KompileOptions options) {
        this.context = context;
        this.options = options;
    }

    @Override
    protected void configure() {
        bind(FrontEnd.class).to(KompileFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KOMPILE);
        bind(Context.class).toInstance(context);
        bind(KompileOptions.class).toInstance(options);
        bind(GlobalOptions.class).toInstance(options.global);
        bind(SMTOptions.class).toInstance(options.experimental.smt);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().toInstance(options);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
        experimentalOptionsBinder.addBinding().toInstance(KompileOptions.Experimental.class);
        experimentalOptionsBinder.addBinding().toInstance(SMTOptions.class);

        MapBinder<String, Backend> mapBinder = MapBinder.newMapBinder(
                binder(), String.class, Backend.class);
        mapBinder.addBinding(Backends.PDF).to(PdfBackend.class);
        mapBinder.addBinding(Backends.LATEX).to(LatexBackend.class);
        mapBinder.addBinding(Backends.DOC).to(DocumentationBackend.class);
        mapBinder.addBinding(Backends.HTML).to(HtmlBackend.class);
        mapBinder.addBinding(Backends.MAUDE).to(KompileBackend.class);
        mapBinder.addBinding(Backends.UNPARSE).to(UnparserBackend.class);
        mapBinder.addBinding(Backends.UNFLATTEN).to(UnflattenBackend.class);
        mapBinder.addBinding(Backends.SYMBOLIC).to(SymbolicBackend.class);
        mapBinder.addBinding(Backends.COQ).to(CoqBackend.class);
    }

    @Provides @Backend.Autoinclude
    boolean autoinclude(Backend backend) {
        return backend.autoinclude();
    }

    @Provides @Backend.AutoincludedFile
    String autoincludedFile(Backend backend) {
        return backend.autoincludedFile();
    }

    @Provides @Backend.Documentation
    boolean documentation(Backend backend) {
        return backend.documentation();
    }

    @Provides
    Backend getBackend(KompileOptions options, Map<String, Backend> map, KExceptionManager kem) {
        Backend backend = map.get(options.backend);
        if (backend == null) {
            kem.registerCriticalError("Invalid backend: " + options.backend
                    + ". It should be one of " + map.keySet());
        }
        return backend;
    }
}
