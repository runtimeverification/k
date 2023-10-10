// Copyright (c) K Team. All Rights Reserved.

package org.kframework.kprove;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;
import org.kframework.unparser.PrintOptions;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BackendOptions;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.InnerParsingOptions;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.SMTOptions;

import java.io.File;
import java.util.Collections;
import java.util.List;

@RequestScoped
public class KProveOptions {
    @Inject
    public KProveOptions() {}

    @ParametersDelegate
    private final transient GlobalOptions global = new GlobalOptions();

    /**
     * Use only in the Guice Provider method, so it can replace the GlobalOptions from kompile.
     */
    public GlobalOptions getGlobalOptions_useOnlyInGuiceProvider() {
        return global;
    }

    @ParametersDelegate
    public DefinitionLoadingOptions definitionLoading = new DefinitionLoadingOptions();

    @ParametersDelegate
    public OuterParsingOptions outerParsing = new OuterParsingOptions();

    @ParametersDelegate
    public InnerParsingOptions innerParsing = new InnerParsingOptions();

    private File specFile;

    public synchronized File specFile(FileUtil files) {
        return outerParsing.mainDefinitionFile(files);
    }

    @ParametersDelegate
    public BackendOptions backend = new BackendOptions();

    @ParametersDelegate
    public SMTOptions smt = new SMTOptions();

    @ParametersDelegate
    public PrintOptions print = new PrintOptions();

    @Parameter(names="--branching-allowed", descriptionKey = "number", arity = 1,
            description="Number of branching events allowed before a forcible stop.")
    public int branchingAllowed = Integer.MAX_VALUE;

    @Parameter(names={"--spec-module", "-sm"}, descriptionKey = "name",
            description="Name of module containing specification to prove")
    public String specModule;

    @Parameter(names="--depth", descriptionKey = "number",
            description="The maximum number of computational steps to prove")
    public Integer depth;

    @Parameter(names="--trusted", descriptionKey = "labels",
            description="Mark this comma separated list of claims as [trusted]")
    public List<String> trusted = null;

    @Parameter(names="--exclude", descriptionKey = "labels", description="Exclude this comma separated list of claims")
    public List<String> exclude = null;

    @Parameter(names="--claims", descriptionKey = "labels", description="Only keep this comma separated list of claims")
    public List<String> claims = null;

    @Parameter(names="--debugger",
            description="Launch proof in an interactive debugger. Currently only supported by the Haskell backend.")
    public boolean debugger;

    @Parameter(names="--debug-script", descriptionKey = "file",
            description="Run script passed in specified file when the debugger starts. Used with --debugger.")
    public String debugScript;

    @Parameter(names="--emit-json", description="Emit JSON serialized main definition for proving.")
    public boolean emitJson = false;

    @Parameter(names="--emit-json-spec", descriptionKey = "file",
            description="If set, emit the JSON serialization of the spec module to the specified file.")
    public String emitJsonSpec = null;
}
