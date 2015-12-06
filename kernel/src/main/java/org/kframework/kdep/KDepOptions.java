// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kdep;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

/**
 * JCommander options for kdep. Essentially, this should contain all the kompile options needed in order to decide what
 * files get slurped by the outer parser.
 */

@RequestScoped
public class KDepOptions {

    @Parameter(description="<file>")
    private List<String> parameters;

    private File mainDefinitionFile;

    public synchronized File mainDefinitionFile() {
        if (mainDefinitionFile == null) {
            if (parameters == null || parameters.size() == 0) {
                throw KEMException.criticalError("You have to provide exactly one main file in order to compute dependencies.");
            }
            mainDefinitionFile = files.get().resolveWorkingDirectory(parameters.get(0));
        }
        return mainDefinitionFile;
    }

    private transient Provider<FileUtil> files;

    @Inject
    public void setFiles(Provider<FileUtil> files) {
        this.files = files;
    }

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the output resides. An output can be either a kompiled K definition or a document which depends on the type of backend. The default is the directory containing the main definition file.")
    public String directory;

    @Parameter(names="-I", description="Add a directory to the search path for requires statements.", variableArity = true)
    public List<String> includes = new ArrayList<>();

    @Parameter(names="--no-prelude", description="Do not implicitly require prelude.k.")
    public boolean noPrelude = false;

}
