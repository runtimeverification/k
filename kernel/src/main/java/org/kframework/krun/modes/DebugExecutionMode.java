// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.krun.modes;

import com.beust.jcommander.JCommander;
import com.beust.jcommander.ParameterException;
import jline.ArgumentCompletor;
import jline.Completor;
import jline.ConsoleReader;
import jline.FileNameCompletor;
import jline.MultiCompletor;
import jline.SimpleCompletor;
import org.kframework.Rewriter;
import org.kframework.debugger.DebuggerState;
import org.kframework.debugger.KDebug;
import org.kframework.debugger.KoreKDebug;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kore.K;
import org.kframework.krun.KRunDebuggerOptions;
import org.kframework.parser.ProductionReference;
import org.kframework.unparser.AddBrackets;
import org.kframework.unparser.KOREToTreeNodes;
import org.kframework.utils.errorsystem.KEMException;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;

/**
 * Created by Manasvi on 6/10/15.
 * <p>
 * Execution mode class for the Kore based Debugger
 */
public class DebugExecutionMode implements ExecutionMode<Void> {

    private static Object command(JCommander jc) {
        return jc.getCommands().get(jc.getParsedCommand()).getObjects().get(0);

    }

    private static String unparseTerm(K input, Module test) {
        return KOREToTreeNodes.toString(
                new AddBrackets(test).addBrackets((ProductionReference)
                        KOREToTreeNodes.apply(KOREToTreeNodes.up(input), test)));
    }

    public static void prettyPrint(CompiledDefinition compiledDef, K result) {

        Module unparsingModule = compiledDef.getParserModule(compiledDef.languageParsingModule());
        System.out.println(unparseTerm(result, unparsingModule) + "\n");

    }

    @Override
    public Void execute(K k, Rewriter rewriter, CompiledDefinition compiledDef) {
        /* Development Purposes Only, will go away in production */
        KDebug debugger = new KoreKDebug(k, rewriter);
        ConsoleReader reader;
        try {
            reader = new ConsoleReader();
        } catch (IOException e) {
            throw KEMException.internalError("IO error detected interacting with console", e);
        }
        reader.setBellEnabled(false);

        List<Completor> argCompletor = new LinkedList<Completor>();
        argCompletor.add(new SimpleCompletor(new String[]{"help",
                "exit", "resume", "step", "search", "select",
                "show-graph", "show-state", "show-transition", "save", "load", "read"}));
        argCompletor.add(new FileNameCompletor());
        List<Completor> completors = new LinkedList<Completor>();
        completors.add(new ArgumentCompletor(argCompletor));
        reader.addCompletor(new MultiCompletor(completors));
        while (true) {
            System.out.println();
            String input;
            try {
                input = reader.readLine("Command > ");
            } catch (IOException e) {
                throw KEMException.internalError("IO error detected interacting with console", e);
            }
            if (input == null) {
                // probably pressed ^D
                System.out.println();
                return null;
            }
            if (input.equals("")) {
                continue;
            }

            KRunDebuggerOptions options = new KRunDebuggerOptions();
            JCommander jc = new JCommander(options);
            jc.addCommand(options.help);
            jc.addCommand(options.step);
            jc.addCommand(options.search);
            jc.addCommand(options.select);
            jc.addCommand(options.showGraph);
            jc.addCommand(options.showState);
            jc.addCommand(options.showTransition);
            jc.addCommand(options.resume);
            jc.addCommand(options.exit);
            jc.addCommand(options.save);
            jc.addCommand(options.load);
            jc.addCommand(options.read);

            try {
                jc.parse(input.split("\\s+"));

                if (jc.getParsedCommand().equals("help")) {
                    if (options.help.command == null || options.help.command.size() == 0) {
                        jc.usage();
                    } else {
                        for (String command : options.help.command) {
                            if (jc.getCommands().containsKey(command)) {
                                jc.usage(command);
                            }
                        }
                    }
                } else if (command(jc) instanceof KRunDebuggerOptions.CommandExit) {
                    return null;

                } else if (command(jc) instanceof KRunDebuggerOptions.CommandResume) {


                } else if (command(jc) instanceof KRunDebuggerOptions.CommandStep) {
                    DebuggerState result = debugger.step(options.step.numSteps);
                    K finalK = result.getCurrentK();
                    if(finalK instanceof K)
                        prettyPrint(compiledDef, (K) finalK);

                } else if (command(jc) instanceof KRunDebuggerOptions.CommandSearch) {


                } else if (command(jc) instanceof KRunDebuggerOptions.CommandSelect) {


                } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowGraph) {


                } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowState) {


                } else if (command(jc) instanceof KRunDebuggerOptions.CommandShowTransition) {

                } else if (command(jc) instanceof KRunDebuggerOptions.CommandSave) {

                } else if (command(jc) instanceof KRunDebuggerOptions.CommandLoad) {

                } else if (command(jc) instanceof KRunDebuggerOptions.CommandRead) {

                } else {
                    assert false : "Unexpected krun debugger command " + jc.getParsedCommand();
                }
            } catch (ParameterException e) {
                System.err.println(e.getMessage());
                jc.usage();
            } catch (IllegalArgumentException | IllegalStateException e) {
                System.err.println(e.getMessage());
            }
        }
    }
}
