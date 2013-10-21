package org.kframework.backend.html;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileFrontEnd;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class HtmlBackend extends BasicBackend {

	public HtmlBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

	@Override
	public void run(Definition definition) throws IOException {
		String fileSep = System.getProperty("file.separator");
		String htmlIncludePath = KPaths.getKBase(false) + fileSep + "include" + fileSep + "html" + fileSep;
		HTMLFilter htmlFilter = new HTMLFilter(htmlIncludePath, context);
		definition.accept(htmlFilter);

		String html = htmlFilter.getHTML();

		FileUtil.saveInFile(GlobalSettings.outputDir + File.separator + FileUtil.stripExtension(new File(definition.getMainFile()).getName()) + ".html", html);

		if (GlobalSettings.verbose) {
			sw.printIntermediate("Generating HTML");
		}

	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}
}
