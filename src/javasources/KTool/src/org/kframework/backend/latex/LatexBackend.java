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

    private File latexifiedFile;

	public LatexBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

    @Override
	public void run(Definition javaDef) {
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
            String latexifiedFilePath = context.dotk.getAbsolutePath() + fileSep + FilenameUtils.removeExtension(canonicalFile.getName()) + ".tex";
            latexifiedFile = new File(latexifiedFilePath);
			FileUtil.save(latexifiedFilePath, latexified);

			if (GlobalSettings.verbose)
				sw.printIntermediate("Latex Generation");

            FileUtils.copyFile(latexifiedFile, new File(GlobalSettings.outputDir + File.separator + latexifiedFile.getName()));
		} catch (IOException e) {
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR, KException.KExceptionGroup.CRITICAL, e.getMessage(), "", ""));
		}
	}

    public File getLatexifiedFile() {
        return latexifiedFile;
    }


	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}
}
