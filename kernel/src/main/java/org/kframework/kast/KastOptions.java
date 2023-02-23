// Copyright (c) K Team. All Rights Reserved.
package org.kframework.kast;

import com.beust.jcommander.IStringConverter;
import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.common.collect.Lists;
import com.google.inject.Inject;
import com.google.inject.Provider;
import org.kframework.attributes.Source;
import org.kframework.kore.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.outer.Outer;
import org.kframework.parser.InputModes;
import org.kframework.unparser.OutputModes;
import org.kframework.unparser.PrintOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.DefinitionLoadingOptions;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.File;
import java.io.Reader;
import java.io.StringReader;
import java.util.Collections;
import java.util.List;

@RequestScoped
public final class KastOptions {

    @Parameter(description="<file>")
    private List<String> parameters;

    public Reader stringToParse() {
        checkFileExprExclusion();
        if (expression != null) {
            return new StringReader(expression);
        }
        checkSingleFile();
        if (parameters.get(0).equals("-")) {
          return new BufferedReader(new InputStreamReader(System.in));
        }
        return files.get().readFromWorkingDirectory(parameters.get(0));
    }

    private void checkFileExprExclusion() {
        if (parameters != null && parameters.size() > 0 && expression != null) {
            throw KEMException.criticalError("It is an error to provide both a file and an expression to parse.");
        }
    }

    private void checkSingleFile() {
        if (parameters != null && parameters.size() > 1) {
            throw KEMException.criticalError("You can only parse one program at a time.");
        }
        if (parameters == null || parameters.size() != 1) {
            throw KEMException.criticalError("You have to provide a file in order to kast a program.");
        }
    }

    private Provider<FileUtil> files;

    @Inject
    public void setFiles(Provider<FileUtil> files) {
        this.files = files;
    }

    /**
     * Get the source of the string to parse. This method is undefined if it is called before calling
     * {@link #stringToParse()}.
     * @return A textual description of the source of the string to parse.
     */
    public Source source() {
        if (expression != null) {
            return Source.apply("<command line: -e>");
        } else {
            return Source.apply(files.get().resolveWorkingDirectory(parameters.get(0)).getAbsolutePath());
        }
    }

    @ParametersDelegate
    public transient GlobalOptions global = new GlobalOptions();

    @ParametersDelegate
    public DefinitionLoadingOptions definitionLoading = new DefinitionLoadingOptions();

    @ParametersDelegate
    public PrintOptions print = new PrintOptions(OutputModes.KAST);

    @Parameter(names={"--gen-parser"}, description="Generate a Bison/Flex parser for the specified module and sort.")
    public boolean genParser;

    @Parameter(names={"--gen-glr-parser"}, description="Generate a Bison/Flex GLR parser for the specified module and sort.")
    public boolean genGlrParser;

    public File bisonOutputFile() {
        checkSingleFile();
        return files.get().resolveWorkingDirectory(parameters.get(0));
    }

    @Parameter(names="--bison-file", description="C file containing functions to link into bison parser.")
    public String bisonFile;

    @Parameter(names="--bison-stack-max-depth", description="Maximum size of bison parsing stack (default: 10000).")
    public long bisonStackMaxDepth = 10000;

    @Parameter(names={"--expression", "-e"}, description="An expression to parse passed on the command " +
    "line. It is an error to provide both this option and a file to parse.")
    private String expression;

    @Parameter(names={"--sort", "-s"}, converter=SortTypeConverter.class, description="The start sort for the default parser. " +
            "The default is the sort of $PGM from the configuration. A sort may also be specified " +
            "with the 'KRUN_SORT' environment variable, in which case it is used if the option is " +
            "not specified on the command line.")
    public Sort sort;

    public static class SortTypeConverter implements IStringConverter<Sort> {
        // converts the command line argument into a Sort
        @Override
        public Sort convert(String arg) {
            return Outer.parseSort(arg);
        }
    }

    @Parameter(names={"--module", "-m"}, description="Parse text in the specified module. Defaults to the syntax module of the definition.")
    public String module;

    @Parameter(names="--expand-macros", description="Also expand macros in the parsed string.")
    public boolean expandMacros = false;

    @Parameter(names={"--input", "-i"}, converter=InputModeConverter.class,
            description="How to read kast input in. <mode> is either [program|binary|kast|json|kore|rule].")
    public InputModes input = InputModes.PROGRAM;

    @Parameter(names={"--steps"}, description="Apply specified kompilation steps to the parsed term. Only for --input rule. Use --steps help for a detailed description of available steps.")
    public List<KastFrontEnd.KompileSteps> steps = Lists.newArrayList(KastFrontEnd.KompileSteps.anonVars);

    public static class InputModeConverter extends BaseEnumConverter<InputModes> {

        public InputModeConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<InputModes> enumClass() {
            return InputModes.class;
        }
    }
}
