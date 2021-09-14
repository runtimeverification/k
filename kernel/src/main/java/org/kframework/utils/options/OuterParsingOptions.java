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
 * Used currently by kompile, and kdep.
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


    @Parameter(names="-I", description="Add a directory to the search path for requires statements.")
    public List<String> includes = new ArrayList<>();

    @Parameter(names="--no-prelude", description="Do not implicitly require prelude.md.")
    public boolean noPrelude = false;

    @Parameter(names="--md-selector", description="Preprocessor: for .md files, select only the md code blocks that match the selector expression. Ex:'k&(!a|b)'.")
    public String mdSelector = "k";

    @Parameter(names="--profile-rule-parsing", description="Generate time in seconds to parse each rule in the semantics. Found in -kompiled directory under timing.log.")
    public String profileRules;
}
