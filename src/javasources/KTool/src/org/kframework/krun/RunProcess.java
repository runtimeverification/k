// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.kframework.kil.loader.Context;
import org.kframework.kil.BackendTerm;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.exceptions.ParseFailedException;
import org.kframework.parser.ParserType;
import org.kframework.parser.ProgramLoader;
import org.kframework.utils.ThreadedStreamCapturer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

// instantiate processes
public class RunProcess {

    private String stdout = null;
    private String err = null;
    private int exitCode;

    public void execute(Map<String, String> environment,String... commands) {

        ThreadedStreamCapturer inputStreamHandler, errorStreamHandler;

        try {
            if (commands.length <= 0) {
                org.kframework.utils.Error.report("Need command options to run");
            }

            // create process
            ProcessBuilder pb = new ProcessBuilder(commands);
            Map<String, String> realEnvironment = pb.environment();
            realEnvironment.putAll(environment);

            // set execution directory to current user dir
            pb.directory(new File(K.userdir));

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
            setExitCode(process.exitValue());

            synchronized (inputStreamHandler) {
                while (inputStreamHandler.isAlive())
                    inputStreamHandler.wait();
            }
            synchronized (errorStreamHandler) {
                while (errorStreamHandler.isAlive())
                    errorStreamHandler.wait();
            }

            String s1 = inputStreamHandler.getContent().toString();
            if (!s1.equals("")) {
                this.setStdout(s1);
            }

            String s2 = errorStreamHandler.getContent().toString();
            // if some errors occurred (if something was written on the stderr stream)
            if (!s2.equals("")) {
                this.setErr(s2);
            }

        } catch (IOException e) {
            // e.printStackTrace();
            org.kframework.utils.Error.report("Error while running process:" + e.getMessage());
        } catch (InterruptedException e) {
            // e.printStackTrace();
            org.kframework.utils.Error.report("Error while running process:" + e.getMessage());
        }

    }

    public Term runParserOrDie(String parser, String pgm, boolean isPgm, String startSymbol, Context context) {
        try {
            return runParser(parser, pgm, isPgm, startSymbol, context);
        } catch (ParseFailedException e) {
            e.report();
            return null;
        }
    }

    /*
     * run the process denoted by the parser ("kast" or an external parser specified with --parser option) and return the AST obtained by parser
     */
    public Term runParser(String parser, String value, boolean isNotFile, String startSymbol, Context context) throws ParseFailedException {
        Term term;

        if (startSymbol == null) {
            startSymbol = context.startSymbolPgm;
        }
        String content = value;

        switch (parser) {
            case "kast":
                if (!isNotFile) {
                    content = FileUtil.getFileContent(value);
                }

                term = ProgramLoader.processPgm(content, value, startSymbol, context, ParserType.PROGRAM);
                break;
            case "kast -e":
                term = ProgramLoader.processPgm(value, value, startSymbol, context, ParserType.PROGRAM);
                break;
            case "kast --parser ground":
                if (!isNotFile) {
                    content = FileUtil.getFileContent(value);
                }
                term = ProgramLoader.processPgm(content, value, startSymbol, context, ParserType.GROUND);
                break;
            case "kast --parser ground -e":
                term = ProgramLoader.processPgm(value, value, startSymbol, context, ParserType.GROUND);
                break;
            case "kast --parser rules":
                if (!isNotFile) {
                    content = FileUtil.getFileContent(value);
                }
                term = ProgramLoader.processPgm(content, value, startSymbol, context, ParserType.RULES);
                break;
            case "kast --parser binary":
                if (!isNotFile) {
                    content = FileUtil.getFileContent(value);
                }
                term = ProgramLoader.processPgm(content, value, startSymbol, context, ParserType.BINARY);
                break;
            default: //external parser
                List<String> tokens = new ArrayList<>(Arrays.asList(parser.split(" ")));
                tokens.add(value);
                Map<String, String> environment = new HashMap<>();
                environment.put("KRUN_SORT", startSymbol);
                environment.put("KRUN_COMPILED_DEF", context.kompiled.getParentFile().getAbsolutePath());
                if (isNotFile) {
                    environment.put("KRUN_IS_NOT_FILE", "true");
                }
                this.execute(environment, tokens.toArray(new String[tokens.size()]));

                if (this.getExitCode() != 0) {
                    throw new ParseFailedException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Parser returned a non-zero exit code: " + this.getExitCode() + "\nStdout:\n" + this.getStdout() + "\nStderr:\n" + this.getErr()));
                }

                String kast = this.getStdout() != null ? this.getStdout() : "";

                //hopefully sort information will get filled in later if we need it, e.g. by SubstitutionFilter
                //TODO(dwightguth): parse the output of the external parser into real kil classes
                term = new BackendTerm("", kast);
        }

        return term;
    }

    // check if the execution of Maude process produced some errors
    public void printError(String content) {
        if (content.contains("GLIBC")) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                    "Error: A known bug in the current version of the Maude rewrite engine\n"
                            + "prohibits running K with I/O on certain architectures.\n"
                            + "If non I/O programs and definitions work but I/O ones fail, \n"
                            + "please let us know and we'll try helping you fix it.\n"));
        } else {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL,
                    content));
        }
    }

    public String getStdout() {
        return stdout;
    }

    public void setStdout(String stdout) {
        this.stdout = stdout;
    }

    public String getErr() {
        return err;
    }

    public void setErr(String err) {
        this.err = err;
    }

    public void setExitCode(int exitCode) {
        this.exitCode = exitCode;
    }

    public int getExitCode() {
        return exitCode;
    }

}
