// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.runner;

import org.kframework.kil.loader.Context;
import org.kframework.utils.file.JarInfo;
import org.kframework.krun.ioserver.main.MainServer;
import org.kframework.krun.tasks.MaudeTask;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;
import java.text.MessageFormat;
import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

public class KRunner {
    // private String _maudeCommand = "maude";
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

    public KRunner(
            File maudeFile,
            File outputFile,
            File errorFile,
            File maudeCommandFile,
            File xmlOutFile,
            String maudeModuleName,
            boolean createLogs,
            boolean noServer,
            Context context) {
        this(maudeFile, 0, false, outputFile, errorFile, maudeCommandFile, xmlOutFile,
                maudeModuleName, createLogs, noServer, context);
    }

    public KRunner(
            File maudeFile,
            int port,
            boolean append,
            File outputFile,
            File errorFile,
            File maudeCommandFile,
            File xmlOutFile,
            String maudeModuleName,
            boolean createLogs,
            boolean noServer,
            Context context) {
        this.context = context;
        this._maudeFile = maudeFile;
        this._maudeFileName = _maudeFile.getAbsolutePath();
        this._maudeCommandFile = maudeCommandFile;
        this._maudeCommandFileName = _maudeCommandFile.getAbsolutePath();
        this._xmlOutFileName = xmlOutFile.getAbsolutePath();
        this._port = port;
        this._append = append;
        this._outputFileName = outputFile.getAbsolutePath();
        this._errorFileName = errorFile.getAbsolutePath();
        this._maudeModule = maudeModuleName;
        this._createLogs = createLogs;
        this._noServer = noServer;

        startLogger();

        if (!_maudeFile.exists()) {
            throw new AssertionError("Something is really wrong with the Maude KRunner: Maude file " + _maudeFileName + " does not exist.");
        }
        if (!_maudeCommandFile.exists()) {
            throw new AssertionError("Something is really wrong with the Maude KRunner: Command file " + _maudeCommandFileName + " does not exist.");
        }
        _logger.info("Maude and command files exist.");
    }

    private void startLogger() {
        _logger = java.util.logging.Logger.getLogger("KRunner");
        if (_createLogs) {
            try {
                FileHandler fh = new FileHandler("krunner.log", _append);
                fh.setFormatter(new SimpleFormatter());
                _logger.addHandler(fh);
            } catch (IOException e) {
                GlobalSettings.kem.registerInternalError("Could not open krunner.log", e);
            }
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

    private static String maudeEscapePath(String original) {
        // backslash-escape white spaces, backslashes, and double quotes
        return original.replaceAll("[\\s\"\\\\]", "\\\\$0");
    }

    public int run() {
        Thread ioServer = null;
        try {
            if (!_noServer) {
                ioServer = startServer();
            }
            _maudeFileName = JarInfo.windowfyPath(_maudeFileName);
            _maudeCommandFileName = JarInfo.windowfyPath(_maudeCommandFileName);
            String commandTemplate = "load {0}\nmod KRUNNER is including {1} .\neq #TCPPORT = {2,number,#} .\nendm\nload {3}\n";
            _maudeFileName = maudeEscapePath(_maudeFileName);
            _maudeCommandFileName = maudeEscapePath(_maudeCommandFileName);

            String command = MessageFormat.format(commandTemplate, _maudeFileName, _maudeModule, _port, _maudeCommandFileName);
            MaudeTask maude = new MaudeTask(command, _outputFileName, _errorFileName, _xmlOutFileName);

            maude.start();
            _logger.info("Maude started");
            _logger.info("Maude command:\n" + command);

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
}
