package org.kframework.backend.latex;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class LatexBackend extends BasicBackend {

    private File latexFile;
    private File latexStyleFile;
    private boolean makeDocument = false;

    public LatexBackend(Stopwatch sw, Context context) {
        super(sw, context);
    }

    public LatexBackend(Stopwatch sw, Context context, boolean doc) {
        super(sw, context);
        makeDocument = doc;
    }

    public void compile(Definition javaDef) throws IOException {
        String fileSep = System.getProperty("file.separator");
        String endl = System.getProperty("line.separator");

        LatexFilter lf;
        if(makeDocument) lf = new DocumentationFilter(context);
        else lf = new LatexFilter(context);
        javaDef.accept(lf);

        String kLatexStyle = KPaths.getKBase(false) + fileSep + "include" + fileSep + "latex" + fileSep + "k.sty";
        latexStyleFile = new File(context.dotk.getAbsolutePath() + fileSep + "k.sty");
        FileUtils.writeStringToFile(latexStyleFile, FileUtil.getFileContent(kLatexStyle));

        String latexified = "\\nonstopmode" + endl +
                "\\PassOptionsToPackage{pdftex,usenames,dvipsnames,svgnames,x11names}{xcolor}"+ endl +
                "\\PassOptionsToPackage{pdftex}{hyperref}"+ endl +
                "\\documentclass{article}" + endl + "\\usepackage[" + options.docStyle() + "]{k}" + endl;
        String preamble = lf.getPreamble().toString();
        latexified += preamble + "\\begin{document}" + endl + lf.getResult() + "\\end{document}" + endl;

        File canonicalFile = options.definition();
        String latexFilePath;
        if(makeDocument) latexFilePath= context.dotk.getAbsolutePath() + fileSep + FilenameUtils.removeExtension(canonicalFile.getName()) + "-doc.tex";
        else latexFilePath = context.dotk.getAbsolutePath() + fileSep + FilenameUtils.removeExtension(canonicalFile.getName()) + ".tex";
        latexFile = new File(latexFilePath);
        FileUtils.writeStringToFile(latexFile, latexified);

        sw.printIntermediate("Latex Generation");
    }

    public void copyFiles() throws IOException {
        FileUtils.copyFile(latexFile, new File(options.directory, latexFile.getName()));
        FileUtils.copyFile(latexStyleFile, new File(options.directory, latexStyleFile.getName()));
    }

    @Override
    public void run(Definition javaDef) {
        try {
            compile(javaDef);
            copyFiles();
        } catch (IOException e) {
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, e.getMessage(), "", ""));
        }
    }

    public File getLatexFile() {
        return latexFile;
    }

    @Override
    public String getDefaultStep() {
        return "FirstStep";
    }
    
    @Override
    public boolean autoinclude(){
        //When the autoinclude stuff gets worked out, uncomment this next line.        
        return !makeDocument;
        //return true;
    }
}
