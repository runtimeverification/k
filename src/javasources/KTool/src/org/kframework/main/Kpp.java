// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.main;

import java.io.*;

public class Kpp {

    private enum State {
        CODE, SINGLE_LINE_COMMENT, MULTI_LINE_COMMENT, STRING
    }

    public static void codeClean(String[] args) {
        if (args.length != 1)
            System.err.println("Usage: kpp <filename>");
        else {
            File f = new File(args[0]);
            if (!f.exists())
                System.err.println("File not found.");

            try (BufferedReader input = new BufferedReader(new FileReader(f))) {
                Kpp.codeClean(input, System.out);
            } catch (IOException e) {
                e.printStackTrace();
            }
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
