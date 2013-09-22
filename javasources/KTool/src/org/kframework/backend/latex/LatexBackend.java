package org.kframework.backend.latex;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class LatexBackend extends BasicBackend {
	public LatexBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

	public static List<File> latex(Definition javaDef, Context context, String mainModule) {
		List<File> result = new ArrayList<File>();
		try {
			Stopwatch sw = new Stopwatch();

			String fileSep = System.getProperty("file.separator");

			LatexFilter lf = new LatexFilter(context);
			javaDef.accept(lf);

			String endl = System.getProperty("line.separator");

			String kLatexStyle = KPaths.getKBase(false) + fileSep + "include" + fileSep + "latex" + fileSep + "k.sty";
			String dotKLatexStyle = context.dotk.getAbsolutePath() + fileSep + "k.sty";

			FileUtil.saveInFile(dotKLatexStyle, FileUtil.getFileContent(kLatexStyle));

			String latexified = "\\nonstopmode" + endl + "\\documentclass{article}" + endl + "\\usepackage[" + GlobalSettings.style + "]{k}" + endl;
			String preamble = lf.getPreamble().toString();
			latexified += preamble + "\\begin{document}" + endl + lf.getResult() + "\\end{document}" + endl;

			File canonicalFile = GlobalSettings.mainFile.getCanonicalFile();
			String latexifiedFile = context.dotk.getAbsolutePath() + fileSep + FileUtil.stripExtension(canonicalFile.getName()) + ".tex";
			result.add(new File(latexifiedFile));
			result.add(new File(dotKLatexStyle));
			FileUtil.saveInFile(latexifiedFile, latexified);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Latex Generation");
			}

		} catch (IOException e1) {
			e1.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}

		return result;
	}

	@Override
	public void run(Definition definition) throws IOException {
		List<File> files = latex(definition, context, definition.getMainModule());
		FileUtil.copyFiles(files, new File(GlobalSettings.outputDir));
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}

}
