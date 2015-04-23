// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.kast;

import java.io.Reader;
import java.io.StringReader;
import java.util.List;

import com.beust.jcommander.IStringConverter;

import org.kframework.attributes.Source;
import org.kframework.kil.Sort;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ParserType;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.RequestScoped;
import org.kframework.utils.options.BaseEnumConverter;
import org.kframework.utils.options.DefinitionLoadingOptions;

import com.beust.jcommander.Parameter;
import com.beust.jcommander.ParametersDelegate;
import com.google.inject.Inject;
import com.google.inject.Provider;

@RequestScoped
public final class KastOptions {

    @Parameter(description="<file>")
    private List<String> parameters;

    public Reader stringToParse() {
        if (parameters != null && parameters.size() > 0 && expression != null) {
            throw KEMException.criticalError("It is an error to provide both a file and an expression to parse.");
        }
        if (expression != null) {
            return new StringReader(expression);
        }
        if (parameters != null && parameters.size() > 1) {
            throw KEMException.criticalError("You can only parse one program at a time.");
        }
        if (parameters == null || parameters.size() != 1) {
            throw KEMException.criticalError("You have to provide a file in order to kast a program.");
        }
        return files.get().readFromWorkingDirectory(parameters.get(0));
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

    @Parameter(names={"--expression", "-e"}, description="An expression to parse passed on the command " +
    "line. It is an error to provide both this option and a file to parse.")
    private String expression;

    @Parameter(names="--parser", converter=ParserTypeConverter.class, description="Choose a parser. <parser> is either [program|newprogram|ground|rule|binary].")
    public ParserType parser = ParserType.PROGRAM;

    public static class ParserTypeConverter extends BaseEnumConverter<ParserType> {

        public ParserTypeConverter(String optionName) {
            super(optionName);
        }

        @Override
        public Class<ParserType> enumClass() {
            return ParserType.class;
        }
    }

    @Parameter(names={"--sort", "-s"}, converter=SortTypeConverter.class, description="The start sort for the default parser. " +
            "The default is the sort of $PGM from the configuration. A sort may also be specified " +
            "with the 'KRUN_SORT' environment variable, in which case it is used if the option is " +
            "not specified on the command line.")
    public Sort sort;

    public static class SortTypeConverter implements IStringConverter<Sort> {
        // converts the command line argument into a Sort
        @Override
        public Sort convert(String arg) {
            return Sort.of(arg);
        }
    }

    @ParametersDelegate
    public Experimental experimental = new Experimental();

    public static final class Experimental {

        @Parameter(names="--pretty", description="Pretty print the output.")
        public boolean pretty = false;

        @Parameter(names="--tab-size", description="How many spaces to use for each indentation level.")
        public int tabSize = 4;

        // we don't specify the default here because it would show up in the usage message and look ugly
        @Parameter(names="--max-width", description="Line will be split before <num> chars.")
        private Integer maxWidth;

        public int maxWidth() {
            if (maxWidth == null) {
                return Integer.MAX_VALUE;
            }
            return maxWidth;
        }

        @Parameter(names="--aux-tab-size", description="How many spaces to indent lines which do not fit into max-width.")
        public int auxTabSize = 2;

        @Parameter(names="--next-line", description="Force newline before first argument.")
        public boolean nextLine = false;
    }
}
