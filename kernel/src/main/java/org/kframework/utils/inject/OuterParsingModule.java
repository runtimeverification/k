// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import org.apache.commons.io.FilenameUtils;
import org.kframework.utils.file.DefinitionDir;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.TempDir;
import org.kframework.utils.file.WorkingDir;
import org.kframework.utils.options.OuterParsingOptions;

import java.io.File;

/**
 * Provides the information needed for tools that parse definitions from source to have acccess to {@link FileUtil}.
 *
 * Used currently by kompile, kdoc, and kdep.
 */
public class OuterParsingModule extends AbstractModule {

    @Override
    protected void configure() {

    }

    @Provides
    @DefinitionDir
    File definitionDir(@WorkingDir File workingDir, OuterParsingOptions options) {
        if (options.directory == null) {
            // bootstrap the part of FileUtil we need
            return options.mainDefinitionFile(new FileUtil(null, null, workingDir, null, null, null)).getParentFile();
        }
        File f = new File(options.directory);
        if (f.isAbsolute()) return f;
        return new File(workingDir, options.directory);
    }

    @Provides @KompiledDir
    File kompiledDir(@DefinitionDir File defDir, OuterParsingOptions options, @WorkingDir File workingDir, @TempDir File tempDir) {
        // bootstrap the part of FileUtil we need
        return new File(defDir, FilenameUtils.removeExtension(options.mainDefinitionFile(new FileUtil(null, null, workingDir, null, null, null)).getName()) + "-kompiled");
    }
}
