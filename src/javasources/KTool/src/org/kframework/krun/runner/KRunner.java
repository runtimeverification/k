// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.runner;

import joptsimple.OptionException;
import joptsimple.OptionParser;
import joptsimple.OptionSet;
import joptsimple.OptionSpec;

import org.kframework.kil.loader.Context;
import org.kframework.krun.K;
import org.kframework.utils.file.KPaths;
import org.kframework.krun.ioserver.main.MainServer;
import org.kframework.krun.tasks.MaudeTask;

import java.io.File;
import java.io.IOException;
import java.text.MessageFormat;
import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

public class KRunner {
    // private String _maudeCommand = "maude";
    private OptionParser _parser = new OptionParser();
    private Logger _logger;

    private File _maudeFile;
    private String _maudeFileName;
    private File _maudeCommandFile;
    private String _maudeCommandFileName;
    private int _port;
    private boolean _append;
    private String _outputFileName;
    private String _errorFileName;
    private String _xmlOutFileName;
    private String _maudeModule;
    private boolean _createLogs;
    private boolean _noServer;
    protected Context context;

    public KRunner(String[] args, Context context, File xmlOutFile) throws IOException {
        this.context = context;
        this._xmlOutFileName = xmlOutFile.getAbsolutePath();
        // boolean append = true;
        // parser.accepts("suppressio");

        OptionSpec<File> maudeFile = _parser.accepts("maudeFile", "Maude file to run").withRequiredArg().required().ofType(File.class);
        OptionSpec<Integer> port = _parser.accepts("port", "Port to use for IO server").withRequiredArg().ofType(Integer.class).defaultsTo(0);
        OptionSpec<Boolean> append = _parser.accepts("appendLogs", "Whether or not messages should be appended to log files").withRequiredArg().ofType(Boolean.class).defaultsTo(false);
        OptionSpec<File> outputFile = _parser.accepts("outputFile", "File to save resulting term").withRequiredArg().ofType(File.class).defaultsTo(new File("/dev/stdout"));
        OptionSpec<File> errorFile = _parser.accepts("errorFile", "File to save any Maude errors").withRequiredArg().ofType(File.class).defaultsTo(new File("/dev/stdout"));
        OptionSpec<File> maudeCommandFile = _parser.accepts("commandFile", "File containing maude command").withRequiredArg().required().ofType(File.class);
        OptionSpec<String> maudeModuleName = _parser.accepts("moduleName", "Final module name").withRequiredArg().required().ofType(String.class);
        OptionSpec<Void> createLogs = _parser.accepts("createLogs", "Create runtime log files");
        OptionSpec<Void> noServer = _parser.accepts("noServer", "Don't start the IO server");

        OptionSet options;
        try {
            options = _parser.parse(args);
            _maudeFile = options.valueOf(maudeFile);
            _maudeFileName = _maudeFile.getAbsolutePath();
            _maudeCommandFile = options.valueOf(maudeCommandFile);
            _maudeCommandFileName = _maudeCommandFile.getAbsolutePath();
            _port = options.valueOf(port);
            _append = options.valueOf(append);
            _outputFileName = options.valueOf(outputFile).getAbsolutePath();
            _errorFileName = options.valueOf(errorFile).getAbsolutePath();
            _maudeModule = options.valueOf(maudeModuleName);
            _createLogs = options.has(createLogs);
            _noServer = options.has(noServer);
        } catch (OptionException e) {
            System.out.println(e.getMessage() + K.lineSeparator);
            throw new AssertionError("Something is really wrong with the Maude KRunner", e);
        }

        startLogger();

        if (!_maudeFile.exists()) {
            throw new AssertionError("Something is really wrong with the Maude KRunner: Maude file " + _maudeFileName + " does not exist.");
        }
        if (!_maudeCommandFile.exists()) {
            throw new AssertionError("Something is really wrong with the Maude KRunner: Command file " + _maudeCommandFileName + " does not exist.");
        }
        _logger.info("Maude and command files exist.");
    }

    private void startLogger() throws IOException {
        _logger = java.util.logging.Logger.getLogger("KRunner");
        if (_createLogs) {
            FileHandler fh = new FileHandler("krunner.log", _append);
            fh.setFormatter(new SimpleFormatter());
            _logger.addHandler(fh);
        }
        _logger.setUseParentHandlers(false);
    }

    Thread startServer() {
        _logger.info("Trying to start server on port " + _port);
        MainServer server = new MainServer(_port, _logger, context);
        Thread t = new Thread(server);
        t.start();
        while (!server._started) {
            Thread.yield();
            // Thread.sleep(500);
        }
        _port = server._port; // in case port was set by server
        _logger.info("Server started on port " + _port);
        return t;
        // Client.main(null);
    }

    public int run() {
        Thread ioServer = null;
        try {
            if (!_noServer) {
                ioServer = startServer();
            }
            _maudeFileName = KPaths.windowfyPath(_maudeFileName);
            _maudeCommandFileName = KPaths.windowfyPath(_maudeCommandFileName);
            String commandTemplate = "load {0}" + K.lineSeparator + "mod KRUNNER is including {1} ." + K.lineSeparator + "eq #TCPPORT = {2,number,#} ." + K.lineSeparator + "endm" + K.lineSeparator + "load {3}" + K.lineSeparator;
            /*_maudeFileName = _maudeFileName.replaceAll("(\\s)", "\\\1");
            _maudeCommandFileName = _maudeCommandFileName.replaceAll("(\\s)", "\\ ");*/
            
            String command = MessageFormat.format(commandTemplate, _maudeFileName, _maudeModule, _port, _maudeCommandFileName);
            MaudeTask maude = new MaudeTask(command, _outputFileName, _errorFileName, _xmlOutFileName);
    
            maude.start();
            _logger.info("Maude started");
            _logger.info("Maude command:" + K.lineSeparator + command);
    
            try {
                maude.join();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            return maude.returnValue;
        } finally {
            if (ioServer != null) {
                ioServer.interrupt();
            }
        }
    }

    public static int main(String[] args, Context context, File xmlOutFile) throws IOException {
        KRunner runner = new KRunner(args, context, xmlOutFile);
        return runner.run();
    }
}
