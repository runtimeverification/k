// Copyright (c) 2015-2019 K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

/**
 * Provides the options needed for tools to perform outer parsing of definitions from source.
 *
 * Used currently by kompile, kdoc, and kdep.
 */
public class OuterParsingOptions implements Serializable {

    public OuterParsingOptions() {}

    @Inject
    public OuterParsingOptions(Void v) {}

    public OuterParsingOptions(File mainDefinitionFile) {
      this.mainDefinitionFile = mainDefinitionFile;
    }

    @Parameter(description="<file>")
    private List<String> parameters;

    private File mainDefinitionFile;

    public synchronized File mainDefinitionFile(FileUtil files) {
        if (mainDefinitionFile == null) {
            if (parameters == null || parameters.size() == 0) {
                throw KEMException.criticalError("You have to provide exactly one main file in order to do outer parsing.");
            }
            mainDefinitionFile = files.resolveWorkingDirectory(parameters.get(0));
        }
        return mainDefinitionFile;
    }

    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the output resides. An output can be either a kompiled K definition or a document which depends on the type of backend. The default is the directory containing the main definition file.")
    public String directory;

    @Parameter(names="-I", description="Add a directory to the search path for requires statements.")
    public List<String> includes = new ArrayList<>();

    @Parameter(names="--no-prelude", description="Do not implicitly require prelude.k.")
    public boolean noPrelude = false;


}
