package org.kframework.krun;

import static org.apache.commons.io.FileUtils.writeStringToFile;

import java.io.IOException;

import org.fusesource.jansi.AnsiString;
import org.kframework.kil.Attributes;
import org.kframework.transformation.Transformation;
import org.kframework.utils.errorsystem.KExceptionManager;

import com.google.inject.Inject;

public class WriteOutput implements Transformation<String, Void> {

    private final KRunOptions options;
    private final KExceptionManager kem;

    @Inject
    public WriteOutput(KRunOptions options, KExceptionManager kem) {
        this.options = options;
        this.kem = kem;
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
            try {
                writeStringToFile(options.experimental.outputFile, output);
            } catch (IOException e) {
                kem.registerInternalError("Could not write to " + options.experimental.outputFile, e);
            }
        }
        return null;
    }

    @Override
    public String getName() {
        return "Write output to user";
    }


}
