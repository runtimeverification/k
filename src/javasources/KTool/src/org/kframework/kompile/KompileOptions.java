// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.kompile;

import java.io.File;
import java.io.Serializable;
import java.util.*;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.coq.CoqBackend;
import org.kframework.backend.html.HtmlBackend;
import org.kframework.backend.java.indexing.IndexingAlgorithm;
import org.kframework.backend.java.symbolic.JavaSymbolicBackend;
import org.kframework.backend.java.symbolic.JavaSymbolicKRun;
import org.kframework.backend.latex.DocumentationBackend;
import org.kframework.backend.latex.LatexBackend;
import org.kframework.backend.latex.PdfBackend;
import org.kframework.backend.maude.KompileBackend;
import org.kframework.backend.maude.krun.MaudeKRun;
import org.kframework.backend.symbolic.SymbolicBackend;
import org.kframework.backend.unparser.UnflattenBackend;
import org.kframework.backend.unparser.UnflattenJavaBackend;
import org.kframework.backend.unparser.UnparserBackend;
import org.kframework.krun.api.KRun;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.SMTOptions;
import org.kframework.utils.options.StringListConverter;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;

public final class KompileOptions implements Serializable {

    public KompileOptions() {}

    //TODO(dwightguth): remove in Guice 4.0
    @Inject
    public KompileOptions(Void v) {}

    public static enum Backend {
        PDF(true, false, PdfBackend.class, null, "autoinclude.k"),
        LATEX(true, false, LatexBackend.class, null, "autoinclude.k"),
        DOC(true, false, DocumentationBackend.class, null, "autoinclude.k"),
        HTML(true, false, HtmlBackend.class, null, "autoinclude.k"),
        MAUDE(false, true, KompileBackend.class, MaudeKRun.class, "autoinclude.k"),
        JAVA(false, true, JavaSymbolicBackend.class, JavaSymbolicKRun.class, "autoinclude-java.k"),
        UNPARSE(false, false, UnparserBackend.class, null, "autoinclude.k"),
        UNFLATTEN(false, false, UnflattenBackend.class, null, "autoinclude.k"),
        UNFLATTEN_JAVA(false, false, UnflattenJavaBackend.class, null, "autoinclude-java.k"),
        SYMBOLIC(false, true, SymbolicBackend.class, MaudeKRun.class, "autoinclude.k"),
        COQ(false, false, CoqBackend.class, null, "autoinclude-java.k");

        private Backend(boolean documentation, boolean generatesDefinition,
                Class<? extends org.kframework.backend.Backend> backend,
                Class<? extends KRun> krun,
                String autoinclude) {
            this.documentation = documentation;
            this.generatesDefinition = generatesDefinition;
            this.backend = backend;
            this.krun = krun;
            this.autoinclude = autoinclude;
        }

        private final boolean documentation;
        private final boolean generatesDefinition;
        private final Class<? extends org.kframework.backend.Backend> backend;
        private final Class<? extends KRun> krun;
        private final String autoinclude;

        /**
         * Represents a backend that generates a documented output file containing the definition
         * in a particular format (e.g. html, pdf, etc)
         */
        public boolean documentation() {
            return documentation;
        }

        /**
         * true if the definition creates a -kompiled directory, false otherwise.
         */
        public boolean generatesDefinition() {
            return generatesDefinition;
        }

        /**
         * The class used to implement Kompile for this backend
         */
        public Class<? extends org.kframework.backend.Backend> backend() {
            return backend;
        }

        /**
         * The class used to implement krun for this backend
         */
        public Class<? extends KRun> krun() {
            return krun;
        }

        public String autoinclude() {
            return autoinclude;
        }
    }

    @Parameter(description="<file>")
    private List<String> parameters;

    public File mainDefinitionFile() {
        if (parameters == null || parameters.size() == 0) {
            GlobalSettings.kem.registerCriticalError("You have to provide exactly one main file in order to compile.");
        }
        return new File(parameters.get(0));
    }

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    // Common options
    /**
     * Directory in which the compiled definition should be put.
     */
    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the output resides. An output can be either a kompiled K definition or a document which depends on the type of backend. The default is the current directory.")
    public File directory = new File(".");

    @Parameter(names="--backend", converter=BackendConverter.class, description="Choose a backend. <backend> is one of [pdf|latex|html|maude|java|unparse|symbolic]. Each of [pdf|latex|html] generates a document from the given K definition. Either of [maude|java] creates the kompiled K definition. 'unparse' generates an unparsed version of the given K definition. 'symbolic' generates symbolic semantics. Experimental: 'doc' generates a .tex document, omitting rules unless specified.")
    public Backend backend = Backend.MAUDE;

    public static class BackendConverter extends BaseEnumConverter<Backend> {

        @Override
        public Class<Backend> enumClass() {
            return Backend.class;
        }
    }

    @Parameter(names="--doc-style", description="Specify a style option for the package 'k.sty' (when '--backend [pdf|latex]' is used) or path to an alternative .css file (when '--backend html' is used).")
    private String docStyle;

    private static final String DEFAULT_DOC_STYLE = "poster,style=bubble";

    public String docStyle() {
        if (backend == Backend.HTML) {
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
    @Parameter(names="--superheat", listConverter=StringListConverter.class, description="Specifies which syntactic constructs superheat the computation. To be used in combination with --supercool. <string> is a comma-separated list of production tags.")
    public List<String> superheat = Collections.singletonList("superheat");

    @Parameter(names="--supercool", listConverter=StringListConverter.class, description="Specifies which rules supercool the computation. To be used in combination with --superheat. <string> is a comma-separated list of rule tags.")
    public List<String> supercool = Collections.singletonList("supercool");

    @Parameter(names="--transition", listConverter=StringListConverter.class, description="<string> is a comma-separated list of tags designating rules to become transitions.")
    public List<String> transition = Collections.singletonList(DEFAULT_TRANSITION);

    public static final String DEFAULT_TRANSITION = "transition";

    @ParametersDelegate
    public Experimental experimental = new Experimental();

    public static final class Experimental implements Serializable {

        // Experimental options
        @Parameter(names="--step", description="Name of the compilation phase after which the compilation process should stop.")
        public String step;

        @Parameter(names="--lib", description="Specify extra-libraries for compile/runtime.")
        public String lib = "";

        @Parameter(names="--add-top-cell", description="Add a top cell to configuration and all rules.")
        public boolean addTopCell = false;

        @Parameter(names="--k-cells", description="Cells which contain komputations.")
        public List<String> kCells = Arrays.asList("k");

        @ParametersDelegate
        public SMTOptions smt = new SMTOptions();

        @Parameter(names="--no-prelude", description="Do not include anything automatically.")
        public boolean noPrelude = false;

        @Parameter(names="--symbolic-rules", listConverter=StringListConverter.class, description="Apply symbolic transformations only to rules annotated with tags from <tags> set. This only has an effect with '--backend symbolic'.")
        public List<String> symbolicRules = Collections.emptyList();

        @Parameter(names="--non-symbolic-rules", listConverter=StringListConverter.class, description="Do not apply symbolic transformations to rules annotated with tags from <tags> set. This only has an effect with '--backend symbolic'.")
        public List<String> nonSymbolicRules = Collections.emptyList();

        @Parameter(names="--kore", description="Generate kore files of a given k definition")
        public boolean kore = false;

        @Parameter(names="--loud", description="Prints 'Done' at the end if all is ok.")
        public boolean loud = false;

        @Parameter(names="--documentation", listConverter=StringListConverter.class, description="<string> is a comma-separated list of tags designating rules to be included in the file generated with --backend=doc")
        public List<String> documentation = Collections.singletonList("documentation");

        @Parameter(names="--rule-index", converter=RuleIndexConveter.class, description="Choose a technique for indexing the rules. <rule-index> is one of [table|path]. (Default: table). This only has effect with '--backend java'.")
        public IndexingAlgorithm ruleIndex = IndexingAlgorithm.RULE_TABLE;

        public static class RuleIndexConveter extends BaseEnumConverter<IndexingAlgorithm> {

            @Override
            public Class<IndexingAlgorithm> enumClass() {
                return IndexingAlgorithm.class;
            }
        }
    }
}
