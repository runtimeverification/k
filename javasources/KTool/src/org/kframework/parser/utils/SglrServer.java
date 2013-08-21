package org.kframework.parser.utils;

import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.IOException;
import java.lang.ProcessBuilder.Redirect;

import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

public final class SglrServer {
    // the sglr-server process
    private static Process server = null;
    private static DataOutputStream output = null;
    private static DataInputStream input = null;

    private static final boolean DEBUG = false;
    
    // A flag signaling whether this is the first time the parser is instantiated.
    private static boolean firstTime = true;

    /** Start the server process */
    private static void init() throws IOException {
        File f = null;
        String basePath = KPaths.getKBase(false);

        if (GlobalSettings.isUnixOS()) {
            f = new File(basePath + "/lib/native/linux/sglr-server");
            f.setExecutable(true, false);
        }
        if (GlobalSettings.isWindowsOS()) {
            f = new File(basePath + "/lib/native/cygwin/sglr-server.exe");
        }
        if (GlobalSettings.isMacOS()) {
            f = new File(basePath + "/lib/native/macosx/sglr-server");
            f.setExecutable(true, false);
        }
        
        ProcessBuilder pb = new ProcessBuilder(f.getAbsolutePath());
        pb.redirectError(Redirect.INHERIT);
        server = pb.start();
        output = new DataOutputStream(server.getOutputStream());
        input = new DataInputStream(server.getInputStream());
        
        firstTime = false;
    }
    
    /**
     * Send the low-order bytes of the string to the process.
     * @param str
     * @throws IOException
     */
    private static void sendString(String str) throws IOException {
        output.writeInt(str.length());
        if (DEBUG) {
            System.err.println("sent length "+str.length());
        }
        output.writeBytes(str);
        if (DEBUG) {
            System.err.println("sent string "+str);
        }
    }

    /**
     * Receive a response from the process
     * @return
     * @throws IOException
     */
    private static byte[] readBytes() throws IOException {
        int len = input.readInt();
        if (DEBUG) {
            System.err.println("read length "+len);
        }
        byte[] bytes = new byte[len];
        input.readFully(bytes);
        if (DEBUG) {
            System.err.println("got bytes");
        }
        return bytes;
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
    public static synchronized byte[] parseString(String parseTablePath, String input, String startSymbol, String inputFileName) throws IOException {
        if (firstTime) {
            init();
        }
        sendString(parseTablePath);
        sendString(input);
        sendString(startSymbol);
        sendString(inputFileName);
        output.flush();
        return readBytes();
    }
}
