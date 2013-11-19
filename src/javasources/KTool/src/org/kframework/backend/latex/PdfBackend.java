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
import org.kframework.utils.errorsystem.KMessages;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;

import static org.apache.commons.io.FileUtils.copyFile;

public class PdfBackend extends BasicBackend {
    public PdfBackend(Stopwatch sw, Context context) {
        super(sw, context);
    }

    private static File generatePdf(File latexFile) {
        Stopwatch sw = new Stopwatch();
        try {
            // Run pdflatex.
            String pdfLatex = "pdflatex";
            String argument = latexFile.getCanonicalPath();

            ProcessBuilder pb = new ProcessBuilder(pdfLatex, argument, "-interaction", "nonstopmode");
            pb.redirectErrorStream(true);
            pb.directory(latexFile.getParentFile());

            Process process = pb.start();
            IOUtils.toString(process.getInputStream());
            process.waitFor();
            if (process.exitValue() != 0)
                GlobalSettings.kem.register(
                        new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1003, "", ""));

            if (GlobalSettings.verbose)
                sw.printIntermediate("Latex2PDF");

            return new File(FilenameUtils.removeExtension(latexFile.getCanonicalPath()) + ".pdf");
        } catch (IOException | InterruptedException e) {
            GlobalSettings.kem.register(
                    new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1001, "", ""));
        }
        return null; // unreachable code
    }

    @Override
    public void run(Definition definition) throws IOException {
        LatexBackend latexBackend = new LatexBackend(sw, context);
        latexBackend.compile(definition);
        File latexFile = latexBackend.getLatexFile();
        File pdfFile = generatePdf(latexFile);
        copyFile(pdfFile, new File(GlobalSettings.outputDir + File.separator + FilenameUtils.removeExtension(new File(definition.getMainFile()).getName()) + ".pdf"));
    }

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }
}
