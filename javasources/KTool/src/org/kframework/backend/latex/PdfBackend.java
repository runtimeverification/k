package org.kframework.backend.latex;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileFrontEnd;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.errorsystem.KMessages;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.*;
import java.util.List;

public class PdfBackend extends BasicBackend {
	public PdfBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

	private static List<File> pdf(List<File> files, String lang) {
		File latexFile = files.get(0);
		files.clear();

		try {
			Stopwatch sw = new Stopwatch();
			// Run pdflatex.
			String pdfLatex = "pdflatex";
			String argument = latexFile.getCanonicalPath();
			// System.out.println(argument);

			ProcessBuilder pb = new ProcessBuilder(pdfLatex, argument, "-interaction", "nonstopmode");
			pb.directory(latexFile.getParentFile());

			pb.redirectErrorStream(true);
			try {
				Process process = pb.start();
				InputStream is = process.getInputStream();
				InputStreamReader isr = new InputStreamReader(is);
				BufferedReader br = new BufferedReader(isr);
				while (br.readLine() != null) {
				}
				process.waitFor();
				if (process.exitValue() != 0) {
					KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1003, "", "");
					GlobalSettings.kem.register(exception);
				}
				process = pb.start();
				is = process.getInputStream();
				isr = new InputStreamReader(is);
				br = new BufferedReader(isr);
				while (br.readLine() != null) {
				}
				process.waitFor();
			} catch (InterruptedException e) {
				e.printStackTrace();
			}

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Latex2PDF");
			}

			files.add(new File(FileUtil.stripExtension(latexFile.getCanonicalPath()) + ".pdf"));
		} catch (IOException e) {
			KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, KMessages.ERR1001, "", "");
			GlobalSettings.kem.register(exception);
		}

		return files;
	}


	@Override
	public void run(Definition definition) throws IOException {
		List<File> files = LatexBackend.latex(definition, context, definition.getMainModule());
		files = pdf(files, definition.getMainModule());
		FileUtil.copyFile(files.get(0).getAbsolutePath(), GlobalSettings.outputDir + File.separator + FileUtil.stripExtension(new File(definition.getMainFile()).getName()) + ".pdf");
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}

}
