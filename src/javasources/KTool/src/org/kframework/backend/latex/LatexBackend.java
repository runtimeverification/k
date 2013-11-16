package org.kframework.backend.latex;

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
import java.util.LinkedList;
import java.util.List;

public class LatexBackend extends BasicBackend {

    private String latexifiedFile;

	public LatexBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

    @Override
	public void run(Definition javaDef) {
        List<File> generatedFiles = new LinkedList<>();
		try {
			Stopwatch sw = new Stopwatch();

			String fileSep = System.getProperty("file.separator");

			LatexFilter lf = new LatexFilter(context);
			javaDef.accept(lf);

			String endl = System.getProperty("line.separator");

			String kLatexStyle = KPaths.getKBase(false) + fileSep + "include" + fileSep + "latex" + fileSep + "k.sty";
			String dotKLatexStyle = context.dotk.getAbsolutePath() + fileSep + "k.sty";

			FileUtil.save(dotKLatexStyle, FileUtil.getFileContent(kLatexStyle));

			String latexified = "\\nonstopmode" + endl + "\\documentclass{article}" + endl + "\\usepackage[" + GlobalSettings.style + "]{k}" + endl;
			String preamble = lf.getPreamble().toString();
			latexified += preamble + "\\begin{document}" + endl + lf.getResult() + "\\end{document}" + endl;

			File canonicalFile = GlobalSettings.mainFile.getCanonicalFile();
            latexifiedFile = context.dotk.getAbsolutePath() + fileSep + FilenameUtils.removeExtension(canonicalFile.getName()) + ".tex";
			generatedFiles.add(new File(latexifiedFile));
			generatedFiles.add(new File(dotKLatexStyle));
			FileUtil.save(latexifiedFile, latexified);

			if (GlobalSettings.verbose)
				sw.printIntermediate("Latex Generation");

            FileUtil.copyFiles(generatedFiles, new File(GlobalSettings.outputDir));
		} catch (IOException e) {
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, e.getMessage(), "", ""));
		}
	}

    public File getLatexifiedFile() {
        return new File(latexifiedFile);
    }


	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}
}
