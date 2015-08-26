// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes.DebugMode;

import com.google.inject.Inject;
import com.google.inject.name.Named;
import jline.console.ConsoleReader;
import jline.console.UserInterruptException;
import jline.console.completer.AggregateCompleter;
import jline.console.completer.ArgumentCompleter;
import jline.console.completer.Completer;
import jline.console.completer.FileNameCompleter;
import jline.console.completer.NullCompleter;
import jline.console.completer.StringsCompleter;
import org.kframework.Rewriter;
import org.kframework.debugger.KDebug;
import org.kframework.debugger.KoreKDebug;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.api.io.FileSystem;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.utils.debugparser.ParseException;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import static org.kframework.utils.debugparser.DebuggerCommandParser.*;
import static org.kframework.utils.file.FileUtil.*;

/**
 * Created by Manasvi on 6/10/15.
 * <p>
 * Execution mode class for the Kore based Debugger
 */
public class DebugExecutionMode implements ExecutionMode<Void> {

    private final KRunOptions kRunOptions;
    private final KExceptionManager kem;
    private final FileUtil files;
    private final FileSystem fileSystem;
    private int checkpointInterval;


    @Inject
    public DebugExecutionMode(KRunOptions kRunOptions, KExceptionManager kem, FileUtil files, @Named("checkpointIntervalValue") Integer checkpointInterval, FileSystem fileSystem) {
        this.kRunOptions = kRunOptions;
        this.kem = kem;
        this.files = files;
        this.checkpointInterval = checkpointInterval;
        this.fileSystem = fileSystem;
    }


    private ConsoleReader getConsoleReader() {
        ConsoleReader reader;
        try {
            reader = new ConsoleReader();
        } catch (IOException e) {
            throw KEMException.internalError("IO error detected interacting with console", e);
        }
        reader.setBellEnabled(false);
        List<String> singleLevelCommands = Arrays.<String>asList("step", "s", "S", "b", "B", "back-step", "j", "J", "jump-to", "quit", "abort", "exit", "src", "source",
                "checkpoint", "ch", "resume", "run", "r", "p", "peek", "remwatch", "xwatch", "show", "get-states", "gs", "select", "copy", "cp", "watch", "w");
        List<String> multiLevelCommands = Arrays.<String>asList("source", "src");

        List<Completer> completers = singleLevelCommands
                .stream()
                .map(command -> (Completer) new ArgumentCompleter(new StringsCompleter(command), new NullCompleter()))
                .collect(Collectors.toList());

        multiLevelCommands.stream()
                .forEach(command -> completers.add(new ArgumentCompleter(new StringsCompleter(command), new FileNameCompleter())));

        reader.addCompleter(new AggregateCompleter(completers));
        return reader;
    }


    @Override
    public Void execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        KDebug debugger = new KoreKDebug(k, rewriter, checkpointInterval, files, kem, kRunOptions, compiledDefinition);

        ConsoleReader reader = getConsoleReader();
        while (true) {
            try {
                String input = reader.readLine("KDebug> ");
                if (input.isEmpty()) {
                    continue;
                }
                Command command = parseCommand(input);
                if (command instanceof Commands.QuitCommand) {
                    break;
                }
                if (command instanceof Commands.SourceCommand) {
                    String source = ((Commands.SourceCommand) command).getSourceFile();
                    processSourceCommand(source, debugger, compiledDefinition);
                    System.out.println("File " + source + " Sourced");
                }
                command.runCommand(debugger, compiledDefinition, false);
            } catch (KEMException e) {
                System.out.println(e.getMessage());
            } catch (ParseException parseException) {
                System.out.println(parseException.getMessage());
            } catch (NumberFormatException numberException) {
                System.out.println("Could not parse \"foo\" as number");
            } catch (FileNotFoundException fileNotFound) {
                System.out.println(fileNotFound.getMessage());
            } catch (IOException inputException) {
                KEMException.criticalError("Failed to read input from console");
            } catch (UserInterruptException | NullPointerException interrupt) {
                return null;
            }
        }
        return null;
    }

    private void processSourceCommand(String srcFile, KDebug debugger, CompiledDefinition compiledDef)
            throws FileNotFoundException, ParseException {
        srcFile = srcFile.replaceFirst("^~", System.getProperty("user.home"));
        String contents = read(new FileReader(srcFile));
        Command command;
        int lineCount = 0;
        for (String line : contents.split(System.getProperty("line.separator"))) {
            lineCount++;
            try {
                if (line.isEmpty()) {
                    continue;
                }
                command = parseCommand(line);
                command.runCommand(debugger, compiledDef, true);
            } catch (ParseException e) {
                System.out.println("File " + srcFile + " Line " + lineCount);
                System.out.println(e.getMessage());
            } catch (KEMException e) {
                System.out.println("File " + srcFile + " Line " + lineCount);
                System.out.println(e.getMessage());
            }
        }
    }

}
