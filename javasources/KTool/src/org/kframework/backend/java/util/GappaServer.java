package org.kframework.backend.java.util;

import org.kframework.utils.ExternalProcessServer;

import java.io.IOException;

public final class GappaServer {
    private static ExternalProcessServer gappaProcess = null;

    private static void init() throws IOException {
        gappaProcess = new ExternalProcessServer("gappa");
        gappaProcess.init();
    }

    /**
     * Method calling the gappa prover.
     * The library is loaded only once and it is persistent.
     * @param input - the string to prove
     * @return true if Gappa managed to prove the property or false if it didn't
     */
    public static boolean prove(String input) {
        try {
            if (gappaProcess == null) init();
            gappaProcess.sendString(input);
            gappaProcess.flushOutput();
            final byte[] bytes = gappaProcess.readBytes();
            String output = new String(bytes);
            return "OK".equals(output);
        } catch (IOException e) {
//            e.printStackTrace();
            gappaProcess = null;
            return false;
        }
    }

    public static boolean proveTrue(String input) {
        return prove("{ " + input + " }");
    }

    public static boolean proveFalse(String input) {
        return prove("{ not( " + input + ") }");
    }
}
