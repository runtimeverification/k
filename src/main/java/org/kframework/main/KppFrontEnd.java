// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.*;

import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.JarInfo;
import org.kframework.utils.inject.FirstArg;

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
            @FirstArg String fileName,
            JarInfo jarInfo) {
        super(kem, globalOptions, USAGE, "", jarInfo);
        this.fileName = fileName;
    }

    public static Module[] getModules(final String[] args) {
        if (args.length != 1) {
            printBootError("Kpp takes exactly one file");
            return null;
        }
        return new Module[] { new AbstractModule() {
            @Override
            protected void configure() {
                bind(FrontEnd.class).to(KppFrontEnd.class);
                bind(Tool.class).toInstance(Tool.OTHER);
                bind(String.class).annotatedWith(FirstArg.class).toInstance(args[0]);
                bind(GlobalOptions.class).toInstance(new GlobalOptions());
            }
        }};
    }

    public boolean run() {
        File f = new File(fileName);
        if (!f.exists())
            System.err.println("File not found.");

        try (BufferedReader input = new BufferedReader(new FileReader(f))) {
            KppFrontEnd.codeClean(input, System.out);
            return true;
        } catch (IOException e) {
            e.printStackTrace();
            return false;
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
