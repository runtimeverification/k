// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.parser.utils;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;

import org.kframework.utils.OS;
import org.kframework.utils.ThreadedStreamCapturer;

public class Sdf2Table {

    public static void run_sdf2table(File startDir, String mainFile) {
        ThreadedStreamCapturer errorStreamHandler;

        try {
            File f = OS.current().getNativeExecutable("sdf2table");

            // create process
            ProcessBuilder pb = new ProcessBuilder(f.getAbsolutePath(), "-c", "-m", mainFile, "-o", mainFile + ".tbl");
            pb.directory(startDir);

            // start sdf2table process
            Process process = pb.start();

            InputStream errorStream = process.getErrorStream();
            // these need to run as java thread to get the standard error from the command.
            errorStreamHandler = new ThreadedStreamCapturer(errorStream);
            errorStreamHandler.start();
            process.waitFor();
            errorStreamHandler.join();

            String s = errorStreamHandler.getContent().toString();
            // if some errors occurred (if something was written on the stderr stream)
            if (!s.equals("")) {
                assert false : "SDF2Table returned errors: " + s;
            }
        } catch (IOException e) {
            e.printStackTrace();
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    public static Thread run_sdf2table_parallel(File startDir, String mainFile) {
        Sdf2Table st = new Sdf2Table();
        Sdf2tableRunner sr = st.new Sdf2tableRunner(startDir, mainFile);

        sr.start();

        return sr;
    }

    private class Sdf2tableRunner extends Thread {
        File startDir;
        String mainFile;

        public Sdf2tableRunner(File startDir, String mainFile) {
            this.startDir = startDir;
            this.mainFile = mainFile;
        }

        public void run() {
            run_sdf2table(startDir, mainFile);
        }
    }

}
