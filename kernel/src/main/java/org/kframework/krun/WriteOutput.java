// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.krun;

import org.fusesource.jansi.AnsiString;
import org.kframework.kil.Attributes;
import org.kframework.transformation.Transformation;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.inject.Main;

import com.google.inject.Inject;

public class WriteOutput implements Transformation<String, Void> {

    private final KRunOptions options;
    private final FileUtil files;

    @Inject
    public WriteOutput(KRunOptions options, @Main FileUtil files) {
        this.options = options;
        this.files = files;
    }

    @Override
    public Void run(String output, Attributes attrs) {
        if (output.isEmpty()) {
            return null;
        }
        if (options.experimental.outputFile == null) {
            System.out.println(output);
        } else {
            output = new AnsiString(output).getPlain().toString();
            files.saveToWorkingDirectory(options.experimental.outputFile, output);
        }
        return null;
    }

    @Override
    public String getName() {
        return "Write output to user";
    }


}
