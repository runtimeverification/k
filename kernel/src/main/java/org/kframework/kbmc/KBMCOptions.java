// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.kbmc;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import org.kframework.main.GlobalOptions;
import org.kframework.unparser.PrintOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.SMTOptions;

import java.io.File;

@RequestScoped
public class KBMCOptions {

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public DefinitionLoadingOptions definitionLoading = new DefinitionLoadingOptions();

    @Parameter(names={"--raw-spec"}, description="Path to a file containing the patterns to model-check." +
            "These patterns will be executed as-is without inserting any initial configuration.")
    public String filePath;

    private File specFile;

    public synchronized File specFile(FileUtil files) {
        if (specFile == null) {
            if (filePath == null || filePath.equals("")) {
                throw KEMException.criticalError("You have to provide exactly one main file in order to do outer parsing.");
            }
            specFile = files.resolveWorkingDirectory(filePath);
        }
        return specFile;
    }

    @ParametersDelegate
    public SMTOptions smt = new SMTOptions();

    @ParametersDelegate
    public PrintOptions print = new PrintOptions();

    @Parameter(names={"--spec-module", "-sm"}, description="Name of module containing specification to model check.")
    public String specModule;

    @Parameter(names={"--def-module", "-m"}, description="Name of module containing definition to model check under.")
    public String defModule;

    @Parameter(names="--depth", description="The maximum number of computational steps to model check.")
    public Integer depth;

    @Parameter(names="--graph-search", description ="Search order of the execution graph. " +
                                                    "Either breadth-first or depth-first.")
    public String graphSearch;

}
