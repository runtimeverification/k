// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kompile;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;
import com.google.inject.Provider;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.Backends;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.StringListConverter;

import java.io.File;
import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

@RequestScoped
public class KompileOptions implements Serializable {

    @Parameter(description="<file>")
    private List<String> parameters;

    private File mainDefinitionFile;

    public File mainDefinitionFile() {
        File m = mainDefinitionFile;
        if (m == null) {
            if (parameters == null || parameters.size() == 0) {
                throw KEMException.criticalError("You have to provide exactly one main file in order to compile.");
            }
            m = mainDefinitionFile = files.get().resolveWorkingDirectory(parameters.get(0));
        }
        return m;
    }

    private transient Provider<FileUtil> files;

    @Inject
    public void setFiles(Provider<FileUtil> files) {
        this.files = files;
    }

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    // Common options
    /**
     * Directory in which the compiled definition should be put.
     */
    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the output resides. An output can be either a kompiled K definition or a document which depends on the type of backend. The default is the directory containing the main definition file.")
    public String directory;

    @Parameter(names="--backend", description="Choose a backend. <backend> is one of [coq|java]. Each creates the kompiled K definition.")
    public String backend = Backends.JAVA;

    @Parameter(names="--doc-style", description="Specify a style option for the package 'k.sty' (when '--backend [pdf|latex]' is used) or path to an alternative .css file (when '--backend html' is used).")
    private String docStyle;

    private static final String DEFAULT_DOC_STYLE = "poster,style=bubble";

    public String docStyle() {
        if (backend == Backends.HTML) {
            if (docStyle == null) {
                return "k-definition.css";
            }
            return docStyle;
        }
        if (docStyle == null) {
            return DEFAULT_DOC_STYLE;
        }
        if (docStyle.startsWith("+")) {
            return DEFAULT_DOC_STYLE + "," + docStyle.substring(1);
        }
        return docStyle;
    }

    @Parameter(names="--main-module", description="Specify main module in which a program starts to execute. This information is used by 'krun'. The default is the name of the given K definition file without the extension (.k).")
    private String mainModule;

    public String mainModule() {
        if (mainModule == null) {
            return FilenameUtils.getBaseName(mainDefinitionFile().getName()).toUpperCase();
        }
        return mainModule;
    }

    @Parameter(names="--syntax-module", description="Specify main module for syntax. This information is used by 'krun'. (Default: <main-module>-SYNTAX).")
    private String syntaxModule;

    public String syntaxModule() {
        if (syntaxModule == null) {
            return mainModule() + "-SYNTAX";
        }
        return syntaxModule;
    }

    // Advanced options
    @Parameter(names="--superheat", listConverter=StringListConverter.class, description="Specifies which syntactic constructs superheat the computation. To be used in combination with --supercool. <string> is a whitespace-separated list of production tags.")
    public List<String> superheat = Collections.singletonList("superheat");

    @Parameter(names="--supercool", listConverter=StringListConverter.class, description="Specifies which rules supercool the computation. To be used in combination with --superheat. <string> is a whitespace-separated list of rule tags.")
    public List<String> supercool = Collections.singletonList("supercool");

    @Parameter(names="--transition", listConverter=StringListConverter.class, description="<string> is a whitespace-separated list of tags designating rules to become transitions.")
    public List<String> transition = Collections.singletonList(DEFAULT_TRANSITION);

    public static final String DEFAULT_TRANSITION = "transition";

    @Parameter(names="--non-strict", description="Do not add runtime sort checks for every variable's inferred sort.")
    private boolean nonStrict;

    public boolean strict() { return !nonStrict; }

    @ParametersDelegate
    public Experimental experimental = new Experimental();

    public static final class Experimental implements Serializable {

        // Experimental options
        @Parameter(names="--step", description="Name of the compilation phase after which the compilation process should stop.")
        public String step;

        @Parameter(names="--add-top-cell", description="Add a top cell to configuration and all rules.")
        public boolean addTopCell = false;

        @Parameter(names="--k-cells", description="Cells which contain komputations.")
        public List<String> kCells = Arrays.asList("k");

        @ParametersDelegate
        public SMTOptions smt = new SMTOptions();

        @Parameter(names="--no-prelude", description="Do not include anything automatically.")
        public boolean noPrelude = false;

        @Parameter(names="--documentation", listConverter=StringListConverter.class, description="<string> is a comma-separated list of tags designating rules to be included in the file generated with --backend=doc")
        public List<String> documentation = Collections.singletonList("documentation");

        @Parameter(names="--legacy-kast", description="Compile with settings based on the old KAST structure")
        public boolean legacyKast = false;

        @Parameter(names="--kore", description="Compile with the new pipeline.")
        public boolean kore = false;
    }
}
