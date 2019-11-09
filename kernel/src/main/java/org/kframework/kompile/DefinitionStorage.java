// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import org.kframework.utils.BinaryLoader;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;

import javax.inject.Inject;
import java.io.File;

/**
 * @author Denis Bogdanas
 * Created on 09-Nov-19.
 */
@RequestScoped
public class DefinitionStorage {
    private final BinaryLoader loader;
    private final FileUtil files;

    @Inject
    public DefinitionStorage(BinaryLoader loader, FileUtil files) {
        this.loader = loader;
        this.files = files;
    }

    public File getCacheFile() {
        return files.resolveKompiled("definitionAndCache.bin");
    }

    public void save(DefinitionAndCache definitionAndCache) {
        if (definitionAndCache.compiledDefinition.kompileOptions.profileRules) {
            definitionAndCache.parseCaches.clear();
        }
        loader.saveOrDie(getCacheFile(), definitionAndCache);
    }

    public DefinitionAndCache load() {
        return loader.loadOrDie(DefinitionAndCache.class, getCacheFile());
    }
}
