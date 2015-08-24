// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes.DebugMode;

import com.beust.jcommander.JCommander;
import com.google.inject.Inject;
import com.google.inject.name.Named;
import jline.ArgumentCompletor;
import jline.Completor;
import jline.ConsoleReader;
import jline.FileNameCompletor;
import jline.MultiCompletor;
import jline.SimpleCompletor;
import org.kframework.Rewriter;
import org.kframework.debugger.KDebug;
import org.kframework.debugger.KoreKDebug;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.modes.ExecutionMode;
import org.kframework.utils.debugparser.ParseException;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import static org.kframework.utils.debugparser.DebuggerCommandParser.*;

/**
 * Created by Manasvi on 6/10/15.
 * <p>
 * Execution mode class for the Kore based Debugger
 */
public class DebugExecutionMode implements ExecutionMode<Void> {

    private final KRunOptions kRunOptions;
    private final KExceptionManager kem;
    private final FileUtil files;
    private int checkpointInterval;

    private static Object command(JCommander jc) {
        return jc.getCommands().get(jc.getParsedCommand()).getObjects().get(0);
    }

    @Inject
    public DebugExecutionMode(KRunOptions kRunOptions, KExceptionManager kem, FileUtil files, @Named("checkpointIntervalValue") Integer checkpointInterval) {
        this.kRunOptions = kRunOptions;
        this.kem = kem;
        this.files = files;
        this.checkpointInterval = checkpointInterval;
    }


    private ConsoleReader getConsoleReader() {
        ConsoleReader reader;
        try {
            reader = new ConsoleReader();
        } catch (IOException e) {
            throw KEMException.internalError("IO error detected interacting with console", e);
        }
        reader.setBellEnabled(false);

        List<Completor> argCompletor = new LinkedList<Completor>();
        argCompletor.add(new SimpleCompletor(new String[]{"help",
                "exit", "step", "jump-to", "back-step", "resume", "run"}));
        argCompletor.add(new FileNameCompletor());
        List<Completor> completors = new LinkedList<Completor>();
        completors.add(new ArgumentCompletor(argCompletor));
        reader.addCompletor(new MultiCompletor(completors));
        return reader;
    }


    @Override
    public Void execute(K k, Rewriter rewriter, CompiledDefinition compiledDefinition) {
        KDebug debugger = new KoreKDebug(k, rewriter, checkpointInterval, files, kem, kRunOptions, compiledDefinition);
        ConsoleReader reader = getConsoleReader();

        while (true) {
            try {
                String input = reader.readLine("KDebug> ");
                Command command = parseCommand(input);
                if (command instanceof Commands.QuitCommand) {
                    break;
                }
                if (command instanceof Commands.SourceCommand) {
                    String source = ((Commands.SourceCommand) command).getSourceFile();
                    processSourceCommand(source);
                }
                command.runCommand(debugger, compiledDefinition);
            } catch (KEMException e) {
                System.out.println(e.getMessage());
            } catch (ParseException parseException) {
                System.out.println(parseException.getMessage());
            } catch (NumberFormatException numberException) {
                System.out.println("Could not parse \"foo\" as number");
            } catch (IOException inputException) {
                KEMException.criticalError("Failed to read input from console");
            }
        }
        return null;
    }

    private void processSourceCommand(String srcFile) {
        System.out.println("Got File " + srcFile);
    }
}
