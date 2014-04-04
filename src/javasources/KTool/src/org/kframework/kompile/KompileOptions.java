package org.kframework.kompile;

import java.io.File;
import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.SMTSolver;
import org.kframework.backend.java.indexing.IndexingAlgorithm;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ExperimentalParserOptions;
import org.kframework.utils.options.BaseEnumConverter;

import com.beust.jcommander.IStringConverter;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParameterException;
import com.beust.jcommander.ParametersDelegate;

public final class KompileOptions implements Serializable {
    
    public static enum Backend {
        PDF(true, false),
        LATEX(true, false),
        DOC(true, false),
        HTML(true, false),
        KORE(false, false),
        MAUDE(false, false),
        JAVA(false, true),
        UNPARSE(false, false),
        UNFLATTEN(false, false),
        UNFLATTEN_JAVA(false, true),
        SYMBOLIC(false, false);
        
        private Backend(boolean documentation, boolean java) {
            this.documentation = documentation;
            this.isJava = java;
        }
        
        private boolean documentation;
        private boolean isJava;
        
        public boolean documentation() {
            return documentation;
        }
        
        public boolean java() {
            return isJava;
        }
    }
    
    @Parameter(description="<file>")
    private List<String> parameters;
    
    public File definition() {
        if (parameters == null || parameters.size() != 1) {
            throw new ParameterException("You have to provide a file in order to compile.");
        }
        return new File(parameters.get(0));
    }
    
    @Parameter(names={"--help", "-h"}, description="Print this help message", help = true)
    public boolean help = false;  
    
    @Parameter(names="--version", description="Print version information")
    public boolean version = false;
    
    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();
    
    // Common options
    @Parameter(names={"--directory", "-d"}, description="Path to the directory in which the output resides. An output can be either a kompiled K definition or a document which depends on the type of backend. The default is the current directory.")
    public File directory = new File(".");
    
    @Parameter(names="--backend", converter=BackendConverter.class, description="Choose a backend. <backend> is one of [pdf|latex|html|maude|java|unparse|symbolic]. Each of [pdf|latex|html] generates a document from the given K definition. Either of [maude|java] creates the kompiled K definition. 'unparse' generates an unparsed version of the given K definition. 'symbolic' generates symbolic semantics. Experimental: 'doc' generates a .tex document, omitting rules unless specified.")
    public Backend backend = Backend.MAUDE;
    
    public static class BackendConverter extends BaseEnumConverter<Backend> implements IStringConverter<Backend> {

        @Override
        public Backend convert(String arg0) {
            return convert(Backend.class, arg0);
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
            return FilenameUtils.getBaseName(definition().getName()).toUpperCase();
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
    
    public static class TagListConverter implements IStringConverter<Set<String>> {
        
        @Override
        public Set<String> convert(String val) {
            String[] parts = val.split("[, ]+");
            Set<String> result = new HashSet<String>();
            for (String part : parts) {
                result.add(part.trim());
            }
            return result;
        }
        
    }
    
    // Advanced options
    @Parameter(names="--superheat", converter=TagListConverter.class, description="Specifies which syntactic constructs superheat the computation. To be used in combination with --supercool. <string> is a comma-separated list of production tags.")
    public Set<String> superheat = Collections.singleton("superheat");
    
    @Parameter(names="--supercool", converter=TagListConverter.class, description="Specifies which rules supercool the computation. To be used in combination with --superheat. <string> is a comma-separated list of rule tags.")
    public Set<String> supercool = Collections.singleton("supercool");
    
    @Parameter(names="--transition", converter=TagListConverter.class, description="<string> is a comma-separated list of tags designating rules to become transitions.")
    public Set<String> transition = Collections.singleton(DEFAULT_TRANSITION);
    
    public static final String DEFAULT_TRANSITION = "transition";
    
    @Parameter(names={"--help-experimental", "-X"}, description="Print help on non-standard options.", help=true)
    public Boolean helpExperimental = false;
    
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
        
        @Parameter(names="--smt", converter=SMTSolverConverter.class, description="SMT solver to use for checking constraints. <solver> is one of [z3|none]. (Default: z3). This only has an effect with '--backend symbolic'.")
        public SMTSolver smt = SMTSolver.Z3;
        
        public static class SMTSolverConverter extends BaseEnumConverter<SMTSolver> implements IStringConverter<SMTSolver> {

            @Override
            public SMTSolver convert(String arg0) {
                return convert(SMTSolver.class, arg0);
            }
        }
        
        @ParametersDelegate
        public transient ExperimentalParserOptions parser = new ExperimentalParserOptions();
        
        @Parameter(names="--no-prelude", description="Do not include anything automatically.")
        public boolean noPrelude = false;
        
        @Parameter(names="--symbolic-rules", converter=TagListConverter.class, description="Apply symbolic transformations only to rules annotated with tags from <tags> set. This only has an effect with '--backend symbolic'.")
        public Set<String> symbolicTags;
        
        @Parameter(names="--non-symbolic-rules", converter=TagListConverter.class, description="Do not apply symbolic transformations to rules annotated with tags from <tags> set. This only has an effect with '--backend symbolic'.")
        public Set<String> nonSymbolicTags;
        
        @Parameter(names="--test-gen", description="Compile for test-case generation purpose in the Java backend. Use concrete sorts and automatically generated labels for heating and cooling rules. This only has an effect with '--backend java'.")
        public boolean testGen = false;
        
        @Parameter(names="--kore", description="Generate kore files of a given k definition")
        public boolean kore = false;
        
        @Parameter(names="--loud", description="Prints 'Done' at the end if all is ok.")
        public boolean loud = false;
             
        @Parameter(names="--documentation", converter=TagListConverter.class, description="<string> is a comma-separated list of tags designating rules to be included in the file generated with --backend=doc")
        public Set<String> documentation = Collections.singleton("documentation");

        @Parameter(names="--rule-index", converter=RuleIndexConveter.class, description="Choose a technique for indexing the rules. <rule-index> is one of [table|path]. (Default: table). This only has effect with '--backend java'.")
        public IndexingAlgorithm ruleIndex = IndexingAlgorithm.RULE_TABLE;
        
        public static class RuleIndexConveter extends BaseEnumConverter<IndexingAlgorithm> implements IStringConverter<IndexingAlgorithm> {

            @Override
            public IndexingAlgorithm convert(String arg0) {
                return convert(IndexingAlgorithm.class, arg0);
            }
        }
    }
}
