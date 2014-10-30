// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.latex;

import org.apache.commons.io.FilenameUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import com.google.inject.Inject;

import java.io.File;

public class LatexBackend extends BasicBackend {

    private String latexFilePath;
    private boolean makeDocument = false;

    private final FileUtil files;

    @Inject
    LatexBackend(Stopwatch sw, Context context, FileUtil files) {
        super(sw, context);
        this.files = files;
    }

    public LatexBackend(Stopwatch sw, Context context, boolean doc, FileUtil files) {
        super(sw, context);
        makeDocument = doc;
        this.files = files;
    }

    public void compile(Definition javaDef) {
        String endl = System.getProperty("line.separator");

        LatexFilter lf;
        if(makeDocument) lf = new DocumentationFilter(context);
        else lf = new LatexFilter(context);
        lf.visitNode(javaDef);

        files.saveToTemp("k.sty", files.loadFromKBase("include/latex/k.sty"));

        String latexified = "\\nonstopmode" + endl +
                "\\PassOptionsToPackage{pdftex,usenames,dvipsnames,svgnames,x11names}{xcolor}"+ endl +
                "\\PassOptionsToPackage{pdftex}{hyperref}"+ endl +
                "\\documentclass{article}" + endl + "\\usepackage[" + options.docStyle() + "]{k}" + endl;
        String preamble = lf.getPreamble().toString();
        latexified += preamble + "\\begin{document}" + endl + lf.getResult() + "\\end{document}" + endl;

        File canonicalFile = options.mainDefinitionFile();
        if(makeDocument) latexFilePath = FilenameUtils.removeExtension(canonicalFile.getName()) + "-doc.tex";
        else latexFilePath = FilenameUtils.removeExtension(canonicalFile.getName()) + ".tex";
        files.saveToTemp(latexFilePath, latexified);

        sw.printIntermediate("Latex Generation");
    }

    public String getLatexFile() {
        return latexFilePath;
    }

    @Override
    public void run(Definition javaDef) {
            compile(javaDef);
            files.copyTempFileToDefinitionDirectory("k.sty");
            files.copyTempFileToDefinitionDirectory(latexFilePath);
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

    @Override
    public boolean documentation() {
        return true;
    }

    @Override
    public boolean generatesDefinition() {
        return false;
    }
}
