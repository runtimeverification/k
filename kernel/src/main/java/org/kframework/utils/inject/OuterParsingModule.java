// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import com.google.inject.AbstractModule;
import com.google.inject.Provides;
import org.apache.commons.io.FilenameUtils;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.DefinitionDir;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KompiledDir;
import org.kframework.utils.file.TempDir;
import org.kframework.utils.file.WorkingDir;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.OutputDirectoryOptions;

import java.io.File;

/**
 * Provides the information needed for tools that parse definitions from source to have access to {@link FileUtil}.
 *
 * Used currently by kompile, and kdep.
 */
public class OuterParsingModule extends AbstractModule {

    @Override
    protected void configure() {

    }

    private boolean exactDirectory = false;

    @Provides
    @DefinitionDir
    File definitionDir(@WorkingDir File workingDir, OuterParsingOptions options, OutputDirectoryOptions output) {
        if (output.outputDirectory != null) {
            if (output.directory != null)
                throw KEMException.criticalError("Cannot use both --directory and --output-kdir at the same time.");
            exactDirectory = true;
            File f = new File(output.outputDirectory);
            if (f.isAbsolute())
                return f;
            return new File(workingDir, output.outputDirectory);
        } else if (output.directory != null) {
            File f = new File(output.directory);
            if (f.isAbsolute())
                return f;
            return new File(workingDir, output.directory);
        }
        // bootstrap the part of FileUtil we need
        return options.mainDefinitionFile(new FileUtil(null, null, workingDir, null, null, null)).getParentFile();
    }

    @Provides @KompiledDir
    File kompiledDir(@DefinitionDir File defDir, OuterParsingOptions options, @WorkingDir File workingDir, @TempDir File tempDir) {
        if (exactDirectory)
            return defDir;
        // bootstrap the part of FileUtil we need
        return new File(defDir, FilenameUtils.removeExtension(options.mainDefinitionFile(new FileUtil(null, null, workingDir, null, null, null)).getName()) + "-kompiled");
    }
}
