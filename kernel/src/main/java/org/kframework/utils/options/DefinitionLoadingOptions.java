// Copyright (c) K Team. All Rights Reserved.
package org.kframework.utils.options;

import com.beust.jcommander.Parameter;
import com.google.inject.Inject;

public class DefinitionLoadingOptions {

    public DefinitionLoadingOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public DefinitionLoadingOptions(Void v) {}

    @Parameter(names={"--directory", "-d"}, description="[DEPRECATED] Path to the directory in which the kompiled " +
            "K definition resides. The default is the unique, only directory with the suffix '-kompiled' " +
            "in the current directory.", descriptionKey = "path", hidden = true)
    public String directory;

    @Parameter(names={"--definition"}, description="Exact path to the kompiled directory.", descriptionKey = "path")
    public String inputDirectory;

    public DefinitionLoadingOptions(String dir) {
        this.directory = dir;
    }
}
