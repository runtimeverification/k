// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.latex;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;

import static org.apache.commons.io.FileUtils.copyFile;

public class PdfBackend extends BasicBackend {
    public PdfBackend(Stopwatch sw, Context context) {
        super(sw, context);
    }

    private File generatePdf(File latexFile) {
        try {
            // Run pdflatex.
            String pdfLatex = "pdflatex";
            String argument = latexFile.getCanonicalPath();

            ProcessBuilder pb = new ProcessBuilder(pdfLatex, argument, "-interaction", "nonstopmode");
            pb.redirectErrorStream(true);
            pb.directory(latexFile.getParentFile());

            Process process = pb.start();
            // Note to the reader from future: In order for `process.waitFor()' to return on Windows,
            // we need to consume process' output and error streams. `pb.redirectErrorStream(true)'
            // and next line does this. Before removing these lines please make sure pdf generation
            // works fine on Windows too.
            // Some more information:
            //    - http://stackoverflow.com/tags/runtime.exec/info
            //    - http://www.javaworld.com/javaworld/jw-12-2000/jw-1229-traps.html?page=1
            // this information is old and apparently not all of them needed with Java 7.
            IOUtils.toString(process.getInputStream());
            process.waitFor();
            if (process.exitValue() != 0) {
                GlobalSettings.kem.register(
                        new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, "pdflatex returned a non-zero exit code.  The pdf might be generated, but with bugs. please inspect the latex logs."));
                copyFile(new File(context.dotk, FilenameUtils.removeExtension(latexFile.getName()) + ".log"), new File(FilenameUtils.removeExtension(latexFile.getName()) + ".log"));
            }
            sw.printIntermediate("Latex2PDF");

            return new File(FilenameUtils.removeExtension(latexFile.getCanonicalPath()) + ".pdf");
        } catch (IOException | InterruptedException e) {
            GlobalSettings.kem.register(
                    new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot generate the pdf version of the definition. It seems that `pdflatex` is not installed or is not in your path. To generate the pdf version you can run `pdflatex` having as argument the latex version of the definition.", "", ""));
        }
        return null; // unreachable code
    }

    @Override
    public void run(Definition definition) throws IOException {
        LatexBackend latexBackend = new LatexBackend(sw, context);
        latexBackend.compile(definition);
        File latexFile = latexBackend.getLatexFile();
        File pdfFile = generatePdf(latexFile);
        if (pdfFile.exists()) {
            copyFile(pdfFile, options.output());
        }
    }

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }
}
