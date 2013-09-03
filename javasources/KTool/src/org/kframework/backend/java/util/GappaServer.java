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
     * @return a byte array in containing the ATerm in the BAF format.
     */
    public static synchronized byte[] prove(String input) {
        try {
            if (gappaProcess == null) init();
            gappaProcess.sendString(input);
            gappaProcess.flushOutput();
            final byte[] bytes = gappaProcess.readBytes();
            return bytes;
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }
}
