// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.krun.tasks;

import org.kframework.krun.K;
import org.kframework.utils.maude.MaudeRun;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

public class MaudeTask extends Thread {
    // private static final String LOG_FILE = "maude.log";
    // private static final String LOGGER = "maude";
    private String _command;
    private String _outputFile;
    private String _errorFile;
    private String _xmlOutFile;
    private Process _maudeProcess;
    public int returnValue;

    public static String maudeExe = MaudeRun.initializeMaudeExecutable();

    public MaudeTask(String command, String outputFile, String errorFile, String xmlOutFile) {
        _command = command;
        _outputFile = outputFile;
        _errorFile = errorFile;
        _xmlOutFile = xmlOutFile;
    }

    @Override
    public void run() {
        try {
            runMaude();
            runCommand();
            returnValue = _maudeProcess.waitFor();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
        }
    }

    private void runMaude() throws IOException {
        ProcessBuilder maude = new ProcessBuilder();
        /*Map<String, String> environment = maude.environment();
        environment.put("MAUDE_LIB", System.getenv("MAUDE_LIB")); */
        List<String> commands = new ArrayList<String>();
        /*if (System.getProperty("os.name").toLowerCase().contains("mac")) {
            commands.add(System.getenv("MAUDE_LIB") + K.fileSeparator + "maude");
        } else {*/
            //commands.add("maude");
            commands.add(maudeExe);
        //}
        commands.add("-no-wrap");
        commands.add("-no-banner");
        commands.add("-xml-log=" + _xmlOutFile);
        maude.command(commands);
        maude.redirectOutput(new File(_outputFile));
        maude.redirectError(new File(_errorFile));

        Process maudeProcess = maude.start();
        _maudeProcess = maudeProcess;
    }

    private void runCommand() throws IOException {
        BufferedWriter maudeInput = new BufferedWriter(new OutputStreamWriter(_maudeProcess.getOutputStream()));
        maudeInput.write(_command + K.lineSeparator);
        maudeInput.close();
    }
}
