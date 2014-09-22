// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.utils.ExternalProcessServer;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

public final class GappaServer {
    private static ExternalProcessServer gappaProcess = null;
    private static boolean initializedRnd = false;
    private static Set<String> initializedVariables = null;
    private static Set<String> uninitializedVariables = null;


    private static void init() throws IOException {
        if (gappaProcess == null) {
            initializedVariables = new HashSet<>();
            uninitializedVariables = new HashSet<>();
            initializedRnd = false;
            gappaProcess = new ExternalProcessServer("gappa");
            gappaProcess.init();
        }
    }

    /**
     * Method calling the gappa prover.
     * The library is loaded only once and it is persistent.
     * @param input - the string to prove
     * @return true if Gappa managed to prove the property or false if it didn't
     */
    public static boolean prove(String input) {
        try {
            init();
            String preamble = "";
            if (!initializedRnd) {
                preamble += "@rnd = float<ieee_64, ne>;\n";
                initializedRnd = true;
            }
            for (String var : uninitializedVariables) {
                preamble += var + " = rnd(dummy" + var + ");\n";
            }
            initializedVariables.addAll(uninitializedVariables);
            uninitializedVariables.clear();
            gappaProcess.sendString(preamble + input);
            gappaProcess.flushOutput();
            final byte[] bytes = gappaProcess.readBytes();
            String output = new String(bytes);
            return "OK".equals(output);
        } catch (IOException e) {
//            e.printStackTrace();
            return false;
        } finally {
            gappaProcess.destroy();
            gappaProcess = null;
        }
    }

    public static boolean proveTrue(String input) {
        return prove("{ " + input + " }");
    }

    public static boolean proveFalse(String input) {
        return prove("{ not( " + input + ") }");
    }

    public static void addVariable(String variable) {
        try {
            init();
        } catch (IOException e) {
            gappaProcess = null;
        }
        if (!initializedVariables.contains(variable))
            uninitializedVariables.add(variable);
    }
}
