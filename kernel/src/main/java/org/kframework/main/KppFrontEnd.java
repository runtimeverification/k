// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.*;
import java.util.ArrayList;
import java.util.List;

import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.Options;

import com.google.inject.AbstractModule;
import com.google.inject.Inject;
import com.google.inject.Module;

public class KppFrontEnd extends FrontEnd {

    private enum State {
        CODE, SINGLE_LINE_COMMENT, MULTI_LINE_COMMENT, STRING
    }

    private final String fileName;
    private static final String USAGE = "Usage: kpp <filename>";

    @Inject
    KppFrontEnd(
            KExceptionManager kem,
            GlobalOptions globalOptions,
            JarInfo jarInfo,
            FileUtil files,
            @Options String[] args) {
        super(kem, globalOptions, USAGE, "", jarInfo, files);
        if (args.length != 1) {
            printBootError("Kpp takes exactly one file");
        }
        this.fileName = args[0];
    }

    public static List<Module> getModules() {
        List<Module> modules = new ArrayList<>();
        modules.add(new AbstractModule() {
            @Override
            protected void configure() {
                bind(FrontEnd.class).to(KppFrontEnd.class);
                bind(Tool.class).toInstance(Tool.KPP);
                bind(GlobalOptions.class).toInstance(new GlobalOptions());
            }
        });
        return modules;
    }

    public int run() {
        File f = new File(fileName);
        if (!f.exists())
            System.err.println("File not found.");

        try (BufferedReader input = new BufferedReader(new FileReader(f))) {
            KppFrontEnd.codeClean(input, System.out);
            return 0;
        } catch (IOException e) {
            throw KEMException.criticalError(e.getMessage(), e);
        }
    }

    public static void codeClean(Reader input, OutputStream out) throws IOException {
        int ch, previous = 0;
        State state = State.CODE;

        while ((ch = input.read()) != -1) {
            switch (state) {
            case SINGLE_LINE_COMMENT:
                if (ch == '\n') {
                    state = State.CODE;
                    previous = 0;
                }
                break;

            case MULTI_LINE_COMMENT:
                if (ch == '/' && previous == '*') {
                    state = State.CODE;
                    previous = ch = 0;
                }
                break;

            case STRING:
                if (previous == '\\' && ch == '\\') {
                    out.write(previous);
                    ch = 0;
                }
                if (previous != '\\' && ch == '"')
                    state = State.CODE;
                break;

            case CODE:
                if (ch == '"')
                    state = State.STRING;
                else if (previous == '/' && ch == '/')
                    state = State.SINGLE_LINE_COMMENT;
                else if (previous == '/' && ch == '*')
                    state = State.MULTI_LINE_COMMENT;
                break;
            }
            if ((state == State.CODE || state == State.STRING) && previous != 0)
                out.write(previous);
            previous = ch;
        }
        if ((state == State.CODE || state == State.STRING) && previous != 0)
            out.write(previous);
        out.flush();
    }
}
