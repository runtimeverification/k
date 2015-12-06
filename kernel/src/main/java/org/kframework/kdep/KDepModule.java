// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kdep;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import com.google.inject.TypeLiteral;
import com.google.inject.multibindings.Multibinder;
import org.apache.commons.io.FilenameUtils;
import org.kframework.main.FrontEnd;
import org.kframework.main.GlobalOptions;
import org.kframework.main.Tool;
import org.kframework.utils.file.DefinitionDir;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.TempDir;
import org.kframework.utils.file.WorkingDir;
import org.kframework.utils.inject.Options;

import java.io.File;

/**
 * Guice module for kdep tool. Binds the information needed to compute the kompiled directory as well as the options
 * and frontend.
 */
public class KDepModule extends AbstractModule {
    @Override
    protected void configure() {

        bind(FrontEnd.class).to(KDepFrontEnd.class);
        bind(Tool.class).toInstance(Tool.KDEP);

        Multibinder<Object> optionsBinder = Multibinder.newSetBinder(binder(), Object.class, Options.class);
        optionsBinder.addBinding().to(KDepOptions.class);
        Multibinder<Class<?>> experimentalOptionsBinder = Multibinder.newSetBinder(binder(), new TypeLiteral<Class<?>>() {}, Options.class);
    }

    @Provides
    GlobalOptions globalOptions(KDepOptions options) {
        return options.global;
    }

    @Provides @DefinitionDir
    File definitionDir(@WorkingDir File workingDir, KDepOptions options) {
        if (options.directory == null) {
            return options.mainDefinitionFile().getParentFile();
        }
        File f = new File(options.directory);
        if (f.isAbsolute()) return f;
        return new File(workingDir, options.directory);
    }

    @Provides @KompiledDir
    File kompiledDir(@DefinitionDir File defDir, KDepOptions options, @TempDir File tempDir) {
        return new File(defDir, FilenameUtils.removeExtension(options.mainDefinitionFile().getName()) + "-kompiled");
    }
}
