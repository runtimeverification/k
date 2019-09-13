// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import org.apache.commons.io.FilenameUtils;

import org.kframework.backend.Backends;
import org.kframework.main.GlobalOptions;
import org.kframework.unparser.OutputModes;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.OuterParsingOptions;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.StringListConverter;

import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

@RequestScoped
public class KompileOptions implements Serializable {


    /**
     * WARNING: this field will be non-null in kompile tool, but null when KompileOption is deserialized,
     * as part of CompiledDefinition, in any other tool. usability depends on context.
     */
    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public OuterParsingOptions outerParsing = new OuterParsingOptions();

    // Common options
    @Parameter(names="--backend", description="Choose a backend. <backend> is one of [ocaml|java|llvm|kore|haskell]. Each creates the kompiled K definition.")
    public String backend = Backends.OCAML;

    private boolean kore;

    @Parameter(names="--main-module", description="Specify main module in which a program starts to execute. This information is used by 'krun'. The default is the name of the given K definition file without the extension (.k).")
    private String mainModule;

    public String mainModule(FileUtil files) {
        if (mainModule == null) {
            return FilenameUtils.getBaseName(outerParsing.mainDefinitionFile(files).getName()).toUpperCase();
        }
        return mainModule;
    }

    @Parameter(names="--syntax-module", description="Specify main module for syntax. This information is used by 'krun'. (Default: <main-module>-SYNTAX).")
    private String syntaxModule;

    public String syntaxModule(FileUtil files) {
        if (syntaxModule == null) {
            return mainModule(files) + "-SYNTAX";
        }
        return syntaxModule;
    }

    @Parameter(names="--transition", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of tags designating rules to become transitions.")
    public List<String> transition = Collections.singletonList(DEFAULT_TRANSITION);

    public static final String DEFAULT_TRANSITION = "transition";

    @Parameter(names="--non-strict", description="Do not add runtime sort checks for every variable's inferred sort.")
    private boolean nonStrict;

    public boolean strict() { return !nonStrict; }

    @Parameter(names="--coverage", description="Generate coverage data when executing semantics.")
    public boolean coverage;

    @Parameter(names="--profile-rule-parsing", description="Generate time in seconds to parse each rule in the semantics. Found in -kompiled directory under timing.log.")
    public boolean profileRules;

    @Parameter(names="--hook-namespaces", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of namespaces to include in the hooks defined in the definition")
    public List<String> hookNamespaces = Collections.emptyList();

    @ParametersDelegate
    public Experimental experimental = new Experimental();

    public boolean isKore() {
        return backend.equals("kore") || backend.equals("haskell") || backend.equals("llvm");
    }

    public static class OutputModeConverter extends BaseEnumConverter<OutputModes> {

        public OutputModeConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<OutputModes> enumClass() {
            return OutputModes.class;
        }
    }

    public static final class Experimental implements Serializable {

        // Experimental options
        @Parameter(names="--step", description="Name of the compilation phase after which the compilation process should stop.")
        public String step;

        @Parameter(names="--add-top-cell", description="Add a top cell to configuration and all rules.")
        public boolean addTopCell = false;

        @Parameter(names="--heat-cool-by-strategies", description="Control heating and cooling using strategies.")
        public boolean heatCoolStrategies = false;

        @Parameter(names="--k-cells", description="Cells which contain komputations.")
        public List<String> kCells = Arrays.asList("k");

        @ParametersDelegate
        public SMTOptions smt = new SMTOptions();

        @Parameter(names="--documentation", listConverter=StringListConverter.class, description="<string> is a comma-separated list of tags designating rules to be included in the file generated with --backend=doc")
        public List<String> documentation = Collections.singletonList("documentation");

        @Parameter(names="--legacy-kast", description="Compile with settings based on the old KAST structure")
        public boolean legacyKast = false;

        @Parameter(names="--kore-prove", description="Compile with the KORE pipeline for proving.")
        public boolean koreProve = false;

        @Parameter(names="--cache-file", description="Location of parse cache file. Default is $KOMPILED_DIR/cache.bin.")
        public String cacheFile;

        @Parameter(names="--emit-json", description="Emit JSON serialized version of parsed and kompiled definitions.")
        public boolean emitJson = false;
    }
}
