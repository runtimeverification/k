// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.krun;

import java.io.BufferedOutputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import org.apache.commons.io.IOUtils;
import org.fusesource.jansi.AnsiOutputStream;
import org.kframework.kil.Attributes;
import org.kframework.transformation.Transformation;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Main;

import com.google.inject.Inject;

public class WriteOutput implements Transformation<InputStream, Void> {

    private final KRunOptions options;
    private final FileUtil files;
    private final Stopwatch sw;

    @Inject
    public WriteOutput(KRunOptions options, @Main FileUtil files, Stopwatch sw) {
        this.options = options;
        this.files = files;
        this.sw = sw;
    }

    @Override
    public Void run(InputStream output, Attributes attrs) {
        try {
            int firstByte = output.read();
            if (firstByte == -1) {
                return null;
            }
            OutputStream out = null;
            try {
                if (options.experimental.outputFile == null) {
                    out = System.out;
                } else {
                    out = new AnsiOutputStream(new BufferedOutputStream(new FileOutputStream(
                            files.resolveWorkingDirectory(options.experimental.outputFile))));
                }
                out.write(firstByte);
                IOUtils.copy(output, out);
                out.write('\n');
            } finally {
                // Not using try-with-resources because we don't want to close System.out
                if (out != null) {
                    if (out == System.out) {
                        out.flush();
                    } else {
                        out.close();
                    }
                }
            }
            return null;
        } catch (IOException e) {
            throw KEMException.criticalError("IO error writing output of krun.", e);
        } finally {
            sw.printIntermediate("Write output to file");
        }
    }

    @Override
    public String getName() {
        return "Write output to user";
    }


}
