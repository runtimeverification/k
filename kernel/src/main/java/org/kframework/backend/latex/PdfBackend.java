// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.latex;

import org.apache.commons.io.FilenameUtils;
import org.apache.commons.io.IOUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;
import com.google.inject.Provider;

import java.io.*;

public class PdfBackend extends BasicBackend {

    private final LatexBackend latexBackend;
    private final FileUtil files;
    private final Provider<ProcessBuilder> pb;

    @Inject
    PdfBackend(
            Stopwatch sw,
            Context context,
            LatexBackend latexBackend,
            FileUtil files,
            Provider<ProcessBuilder> pb) {
        super(sw, context);
        this.latexBackend = latexBackend;
        this.files = files;
        this.pb = pb;
    }

    private String generatePdf(File latexFile) {
        try {
            // Run pdflatex.
            String pdfLatex = "pdflatex";
            String argument = latexFile.getCanonicalPath();

            ProcessBuilder pb = this.pb.get().command(
                    pdfLatex, argument, "-interaction", "nonstopmode");
            pb.redirectErrorStream(true);
            pb.directory(latexFile.getParentFile());

            Process process = pb.start();
            // Note to the reader from future: In order for `process.waitFor()' to return on Windows
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
                String latexLogFile = FilenameUtils.removeExtension(latexFile.getName()) + ".log";
                files.copyTempFileToDefinitionDirectory(latexLogFile);
                throw KExceptionManager.criticalError("pdflatex returned a non-zero exit code. " +
                                "The pdf might be generated, but with bugs. " +
                                "Please inspect the latex logs.");
            }
            sw.printIntermediate("Latex2PDF");

            return FilenameUtils.removeExtension(latexFile.getName()) + ".pdf";
        } catch (IOException | InterruptedException e) {
            throw KExceptionManager.criticalError(
                            "Cannot generate the pdf version of the definition. " +
                            "It seems that `pdflatex` is not installed or is not in your path. " +
                            "To generate the pdf version you can run `pdflatex` having as " +
                            "argument the latex version of the definition.", e);
        }
    }

    @Override
    public void run(Definition definition) {
        latexBackend.compile(definition);
        String latexFile = latexBackend.getLatexFile();
        String pdfFile = generatePdf(files.resolveTemp(latexFile));
        files.copyTempFileToDefinitionDirectory(pdfFile);
    }

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }

    @Override
    public boolean documentation() {
        return true;
    }

    @Override
    public boolean generatesDefinition() {
        return false;
    }
}
