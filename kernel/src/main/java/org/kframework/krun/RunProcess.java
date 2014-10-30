// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.loader.Context;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Sort;
import org.kframework.kil.Source;
import org.kframework.kil.Sources;
import org.kframework.kil.Term;
import org.kframework.parser.ParserType;
import org.kframework.parser.ProgramLoader;
import org.kframework.utils.ThreadedStreamCapturer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.ParseFailedException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.Environment;
import org.kframework.utils.file.WorkingDir;

import com.google.inject.Inject;
import com.google.inject.Provider;

import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

// instantiate processes
public class RunProcess {

    public static class ProcessOutput {
        public final String stdout;
        public final String stderr;
        public final int exitCode;

        public ProcessOutput(String stdout, String stderr, int exitCode) {
            this.stdout = stdout;
            this.stderr = stderr;
            this.exitCode = exitCode;
        }
    }

    private final KExceptionManager kem;
    private final ProgramLoader loader;
    private final Provider<ProcessBuilder> pb;

    @Inject
    public RunProcess(KExceptionManager kem, ProgramLoader loader, Provider<ProcessBuilder> pb) {
        this.kem = kem;
        this.loader = loader;
        this.pb = pb;
    }

    public KExceptionManager getKem() {
        return kem;
    }

    public ProcessOutput execute(Map<String, String> environment, String... commands) {

        ThreadedStreamCapturer inputStreamHandler, errorStreamHandler;

        try {
            if (commands.length <= 0) {
                throw KExceptionManager.criticalError("Need command options to run");
            }

            // create process
            ProcessBuilder pb = this.pb.get().command(commands);
            Map<String, String> realEnvironment = pb.environment();
            realEnvironment.putAll(environment);

            // start process
            Process process = pb.start();

            InputStream inputStream = process.getInputStream();
            InputStream errorStream = process.getErrorStream();
            // these need to run as java threads to get the standard output and error from the command.
            inputStreamHandler = new ThreadedStreamCapturer(inputStream);
            errorStreamHandler = new ThreadedStreamCapturer(errorStream);

            inputStreamHandler.start();
            errorStreamHandler.start();

            // wait for process to finish
            process.waitFor();

            synchronized (inputStreamHandler) {
                while (inputStreamHandler.isAlive())
                    inputStreamHandler.wait();
            }
            synchronized (errorStreamHandler) {
                while (errorStreamHandler.isAlive())
                    errorStreamHandler.wait();
            }

            String s1 = inputStreamHandler.getContent().toString();

            String s2 = errorStreamHandler.getContent().toString();

            return new ProcessOutput(s1, s2, process.exitValue());

        } catch (IOException | InterruptedException e) {
            throw KExceptionManager.criticalError("Error while running process:" + e.getMessage(), e);
        }

    }

    /*
     * run the process denoted by the parser ("kast" or an external parser specified with --parser option) and return the AST obtained by parser
     */
    public Term runParser(String parser, String value, boolean isNotFile, Sort startSymbol, Context context) throws ParseFailedException {
        Term term;

        if (startSymbol == null) {
            startSymbol = context.startSymbolPgm;
        }
        String content = value;
        Source source = Sources.fromCommandLine("parameters");

        switch (parser) {
            case "kast":
                if (!isNotFile) {
                    content = context.files.loadFromWorkingDirectory(value);
                    source = Sources.fromFile(context.files.resolveWorkingDirectory(value));
                }
                term = loader.processPgm(content, source, startSymbol, context, ParserType.PROGRAM);
                break;
            case "kast -e":
                term = loader.processPgm(value, source, startSymbol, context, ParserType.PROGRAM);
                break;
            case "kast --parser ground":
                if (!isNotFile) {
                    content = context.files.loadFromWorkingDirectory(value);
                    source = Sources.fromFile(context.files.resolveWorkingDirectory(value));
                }
                term = loader.processPgm(content, source, startSymbol, context, ParserType.GROUND);
                break;
            case "kast --parser ground -e":
                term = loader.processPgm(value, source, startSymbol, context, ParserType.GROUND);
                break;
            case "kast --parser rules":
                if (!isNotFile) {
                    content = context.files.loadFromWorkingDirectory(value);
                    source = Sources.fromFile(context.files.resolveWorkingDirectory(value));
                }
                term = loader.processPgm(content, source, startSymbol, context, ParserType.RULES);
                break;
            case "kast --parser binary":
                if (!isNotFile) {
                    content = context.files.loadFromWorkingDirectory(value);
                    source = Sources.fromFile(context.files.resolveWorkingDirectory(value));
                }
                term = loader.processPgm(content, source, startSymbol, context, ParserType.BINARY);
                break;
            default: //external parser
                List<String> tokens = new ArrayList<>(Arrays.asList(parser.split(" ")));
                tokens.add(value);
                Map<String, String> environment = new HashMap<>();
                environment.put("KRUN_SORT", startSymbol.toString());
                environment.put("KRUN_COMPILED_DEF", context.files.resolveDefinitionDirectory(".").getAbsolutePath());
                if (isNotFile) {
                    environment.put("KRUN_IS_NOT_FILE", "true");
                }
                ProcessOutput output = this.execute(environment, tokens.toArray(new String[tokens.size()]));

                if (output.exitCode != 0) {
                    throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Parser returned a non-zero exit code: "
                            + output.exitCode + "\nStdout:\n" + output.stdout + "\nStderr:\n" + output.stderr));
                }

                String kast = output.stdout != null ? output.stdout : "";

                //hopefully sort information will get filled in later if we need it, e.g. by SubstitutionFilter
                //TODO(dwightguth): parse the output of the external parser into real kil classes
                term = new BackendTerm(Sort.of(""), kast);
        }

        return term;
    }

}
