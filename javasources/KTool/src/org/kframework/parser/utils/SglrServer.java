package org.kframework.parser.utils;

import org.kframework.utils.ExternalProcessServer;

import java.io.IOException;

public final class SglrServer {
    private static ExternalProcessServer sglrProcess = null;

    private static void init() throws IOException {
        sglrProcess = new ExternalProcessServer("sglr-server");
        sglrProcess.init();
    }

    /**
     * The main parsing function that accesses the C parser in native way.
     * The library is loaded only once and it is persistent.
     * @param parseTablePath - the path to the parse table. Note that it will be cached.
     * @param input - the string to parse
     * @param startSymbol - the start sort
     * @param inputFileName - this is required to annotate the nodes with location information. It can be any string.
     * @return a byte array in containing the ATerm in the BAF format.
     */
    public static synchronized byte[] parseString(String parseTablePath, String input, String startSymbol, String inputFileName) {
        try {
            if (sglrProcess == null) init();
            sglrProcess.sendString(parseTablePath);
            sglrProcess.sendString(input);
            sglrProcess.sendString(startSymbol);
            sglrProcess.sendString(inputFileName);
            sglrProcess.flushOutput();
            return sglrProcess.readBytes();
        } catch (IOException e) {
            e.printStackTrace();
            return null;
        }
    }
}
