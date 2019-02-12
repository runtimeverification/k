package org.kframework.krun;

import com.google.inject.AbstractModule;
import com.google.inject.Provider;
import com.google.inject.Provides;
import org.kframework.definition.Definition;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.rewriter.Rewriter;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.Map;
import java.util.function.Function;

public class RewriterModule extends AbstractModule {
    @Override
    protected void configure() {
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
