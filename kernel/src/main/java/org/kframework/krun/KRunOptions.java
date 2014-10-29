// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.lang3.tuple.Pair;
import org.kframework.backend.unparser.OutputModes;
import org.kframework.kil.loader.Context;
import org.kframework.krun.api.SearchType;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.DefinitionLoadingOptions;
import org.kframework.utils.options.OnOffConverter;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.StringListConverter;

import com.beust.jcommander.DynamicParameter;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;

public final class KRunOptions {

    public KRunOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public KRunOptions(Void v) {}

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public ConfigurationCreationOptions configurationCreation = new ConfigurationCreationOptions();

    public static final class ConfigurationCreationOptions {

        public ConfigurationCreationOptions() {}

        //TODO(dwightguth): remove in Guice 4.0
        @Inject
        public ConfigurationCreationOptions(Void v) {}

        @Parameter(description="<file>")
        private List<String> parameters;

        public String pgm() {
            if (parameters == null || parameters.size() == 0) {
                return null;
            }
            if (parameters.size() > 1) {
                throw KExceptionManager.criticalError("You can only specify $PGM on the command line itself");
            }
            return parameters.get(0);
        }

        @ParametersDelegate
        public DefinitionLoadingOptions definitionLoading = new DefinitionLoadingOptions();

        @Parameter(names={"--parser"}, description="Command used to parse programs. Default is \"kast\"")
        private String parser;

        public String parser(Context context) {
            if (parser == null) {
                if (term()) {
                    return "kast --parser ground";
                } else {
                    return "kast";
                }
            } else {
                return parser;
            }
        }

        @DynamicParameter(names={"--config-parser", "-p"}, description="Command used to parse " +
                "configuration variables. Default is \"kast --parser ground -e\". See description of " +
                "--parser. For example, -cpPGM=\"kast\" specifies that the configuration variable $PGM " +
                "should be parsed with the command \"kast\".")
        private Map<String, String> configVarParsers = new HashMap<>();

        @DynamicParameter(names={"--config-var", "-c"}, description="Specify values for variables in the configuration.")
        private Map<String, String> configVars = new HashMap<>();

        public Map<String, Pair<String, String>> configVars(Context context) {
            Map<String, Pair<String, String>> result = new HashMap<>();
            for (Map.Entry<String, String> entry : configVars.entrySet()) {
                String cfgParser = "kast --parser ground -e";
                if (configVarParsers.get(entry.getKey()) != null) {
                    cfgParser = configVarParsers.get(entry.getKey());
                }
                result.put(entry.getKey(), Pair.of(entry.getValue(), cfgParser));
            }
            if (!term() && pgm() != null) {
                if (configVars.containsKey("PGM")) {
                    throw KExceptionManager.criticalError("Cannot specify both -cPGM and a program to parse.");
                }
                result.put("PGM", Pair.of(pgm(), parser(context)));
            }
            return result;
        }

        @Parameter(names="--term", description="Input argument will be parsed with the specified parser and used as the sole input to krun.")
        private boolean term = false;

        public boolean term() {
            if (term && configVars.size() > 0) {
                throw KExceptionManager.criticalError("You cannot specify both the term and the configuration variables.");
            }
            if (term && pgm() == null) {
                throw KExceptionManager.criticalError("You must specify something to parse with the --term option.");
            }
            return term;
        }
    }

    @Parameter(names="--io", description="Use real IO when running the definition. Defaults to true.", arity=1,
            converter=OnOffConverter.class)
    private Boolean io;

    public boolean io() {
        if (io != null && io == true && search()) {
            throw KExceptionManager.criticalError("You cannot specify both --io on and --search");
        }
        if (io != null && io == true && experimental.ltlmc() != null) {
            throw KExceptionManager.criticalError("You cannot specify both --io on and --ltlmc");
        }
        if (io != null && io == true && experimental.debugger()) {
            throw KExceptionManager.criticalError("You cannot specify both --io on and --debugger");
        }
        if (search()
                || experimental.prove != null
                || experimental.ltlmc() != null
                || experimental.debugger()) {
            return false;
        }
        if (io == null) {
            return true;
        }
        return io;
    }

    @ParametersDelegate
    public ColorOptions color = new ColorOptions();

    @Parameter(names={"--output", "-o"}, converter=OutputModeConverter.class,
            description="How to display Maude results. <mode> is either [pretty|smart|compatible|kore|raw|binary|none].")
    public OutputModes output = OutputModes.PRETTY;

    public static class OutputModeConverter extends BaseEnumConverter<OutputModes> {

        public OutputModeConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<OutputModes> enumClass() {
            return OutputModes.class;
        }
    }

    @Parameter(names="--search", description="In conjunction with it you can specify 3 options that are optional: pattern (the pattern used for search), bound (the number of desired solutions) and depth (the maximum depth of the search).")
    private boolean search = false;

    @Parameter(names="--search-final", description="Same as --search but only return final states, even if --depth is provided.")
    private boolean searchFinal = false;

    @Parameter(names="--search-all", description="Same as --search but return all matching states, even if --depth is not provided.")
    private boolean searchAll = false;

    @Parameter(names="--search-one-step", description="Same as --search but search only one transition step.")
    private boolean searchOneStep = false;

    @Parameter(names="--search-one-or-more-steps", description="Same as --search-all but exclude initial state, even if it matches.")
    private boolean searchOneOrMoreSteps = false;

    public boolean search() {
        return search || searchFinal || searchAll || searchOneStep || searchOneOrMoreSteps;
    }

    public SearchType searchType() {
        if (search) {
            if (searchFinal || searchAll || searchOneStep || searchOneOrMoreSteps) {
                throw KExceptionManager.criticalError("You can specify only one type of search.");
            }
            if (depth != null) {
                return SearchType.STAR;
            }
            return SearchType.FINAL;
        } else if (searchFinal) {
            if (searchAll || searchOneStep || searchOneOrMoreSteps) {
                throw KExceptionManager.criticalError("You can specify only one type of search.");
            }
            return SearchType.FINAL;
        } else if (searchAll) {
            if (searchOneStep || searchOneOrMoreSteps) {
                throw KExceptionManager.criticalError("You can specify only one type of search.");
            }
            return SearchType.STAR;
        } else if (searchOneStep) {
            if (searchOneOrMoreSteps) {
                throw KExceptionManager.criticalError("You can specify only one type of search.");
            }
            return SearchType.ONE;
        } else if (searchOneOrMoreSteps) {
            return SearchType.PLUS;
        } else {
            return null;
        }
    }

    @Parameter(names="--pattern", description="Specify a term and/or side condition that the result of execution or search must match in order to succeed. Return the resulting matches as a list of substitutions. In conjunction with it you can specify other 2 options that are optional: bound (the number of desired solutions) and depth (the maximum depth of the search).")
    public String pattern;

    public static final String DEFAULT_PATTERN = "<generatedTop> B:Bag </generatedTop> [anywhere]";


    @Parameter(names="--bound", description="The number of desired solutions for search.")
    public Integer bound;

    @Parameter(names="--depth", description="The maximum number of computational steps to execute or search the definition for.")
    public Integer depth;

    @Parameter(names="--graph", description="Displays the search graph generated by the last search.")
    public boolean graph = false;

    @ParametersDelegate
    public Experimental experimental = new Experimental();

    public final class Experimental {

        @Parameter(names="--simulation", description="Simulation property of two programs in two semantics.",
                listConverter=StringListConverter.class)
        public List<String> simulation;

        @Parameter(names="--statistics", description="Print rewrite engine statistics.", arity=1,
                converter=OnOffConverter.class)
        public boolean statistics = false;

        @Parameter(names="--debugger", description="Run an execution in debug mode.")
        private boolean debugger = false;

        public boolean debugger() {
            if (debugger && search()) {
                throw new ParameterException("Cannot specify --search with --debug. In order to search inside the debugger, use the step-all command.");
            }
            return debugger;
        }

        @Parameter(names="--ltlmc", description="Specify the formula for model checking at the commandline.")
        private String ltlmc;

        @Parameter(names="--ltlmc-file", description="Specify the formula for model checking through a file.")
        private String ltlmcFile;

        public String ltlmc() {
            if (ltlmc != null && ltlmcFile != null) {
                throw new ParameterException("You may specify only one of --ltlmc and --ltlmc-file.");
            }
            if (ltlmc != null) {
                return ltlmc;
            }
            if (ltlmcFile == null) {
                return null;
            }
            return files.loadFromWorkingDirectory(ltlmcFile);
        }

        private FileUtil files;

        @Inject
        public void setFiles(FileUtil files) {
            this.files = files;
        }

        @Parameter(names="--prove", description="Prove a set of reachability rules.")
        public String prove;

        @ParametersDelegate
        public SMTOptions smt = new SMTOptions();

        @Parameter(names="--output-file", description="Store output in the file instead of displaying it.")
        public String outputFile;
    }
}
