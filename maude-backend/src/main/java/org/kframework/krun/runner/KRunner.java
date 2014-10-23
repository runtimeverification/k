// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.runner;

import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.kompile.KompileOptions;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.ioserver.main.IOServer;
import org.kframework.utils.maude.MaudeRun;

import com.google.inject.Inject;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.List;

public class KRunner {
    private final FileUtil files;
    private final KompileOptions kompileOptions;
    private final KRunOptions krunOptions;
    private final IOServer server;

    @Inject
    public KRunner(
            FileUtil files,
            KompileOptions kompileOptions,
            KRunOptions krunOptions,
            IOServer server) {
        this.files = files;
        this.kompileOptions = kompileOptions;
        this.krunOptions = krunOptions;
        this.server = server;
    }

    Thread startServer() {
        Thread t = new Thread(server);
        t.start();
        return t;
    }

    private Process runMaude() throws IOException {
        ProcessBuilder maude = new ProcessBuilder();
        List<String> commands = new ArrayList<String>();
        commands.add(MaudeRun.initializeMaudeExecutable());
        commands.add("-no-wrap");
        commands.add("-no-banner");
        commands.add("-xml-log=" + files.resolveTemp("maudeoutput.xml").getAbsolutePath());
        maude.command(commands);
        maude.redirectOutput(files.resolveTemp("maude_out"));
        maude.redirectError(files.resolveTemp("maude_err"));

        return maude.start();
    }

    public int run() {
        Thread ioServer = null;
        try {
            if (krunOptions.io()) {
                synchronized(server) {
                    ioServer = startServer();
                    server.wait();
                }
            }
            String commandTemplate = "load {0}\nmod KRUNNER is including {1} .\neq #TCPPORT = {2,number,#} .\nendm\nload {3}\n";

            String command = MessageFormat.format(commandTemplate,
                    files.resolveKompiled("main.maude").getAbsolutePath(),
                    kompileOptions.mainModule(), server.getPort(), files.resolveTemp("maude_in").getAbsolutePath());
            Process _maudeProcess = runMaude();
            BufferedWriter maudeInput = new BufferedWriter(new OutputStreamWriter(_maudeProcess.getOutputStream()));
            maudeInput.write(command + "\n");
            maudeInput.close();
            try {
                _maudeProcess.waitFor();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return 1;
            }
            return _maudeProcess.exitValue();
        } catch (IOException e1) {
            throw KExceptionManager.internalError("Error running maude: " + e1.getMessage(), e1);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return 1;
        } finally {
            if (ioServer != null) {
                ioServer.interrupt();
            }
        }
    }
}
