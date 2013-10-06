package org.kframework.backend.doc;

import org.kframework.backend.BasicBackend;
import org.kframework.backend.html.HTMLFilter;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class DocumentationBackend extends BasicBackend {
	public DocumentationBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

	@Override
	public void run(Definition definition) throws IOException {
		String fileSep = System.getProperty("file.separator");
		String htmlIncludePath = KPaths.getKBase(false) + fileSep + "include" + fileSep + "html" + fileSep;
		HTMLFilter htmlFilter = new HTMLFilter(htmlIncludePath, context);
		definition.accept(htmlFilter);

		String html = htmlFilter.getHTML();

		FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/def.html", html);

		FileUtil.saveInFile(GlobalSettings.outputDir + fileSep + FileUtil.stripExtension(GlobalSettings.mainFile.getName()) + ".html", html);
		String kHTMLStyle = KPaths.getKBase(false) + fileSep + "include" + fileSep + "html" + fileSep + GlobalSettings.style;
		final String toFile = GlobalSettings.outputDir + fileSep + GlobalSettings.style;
		FileUtil.copyFile(kHTMLStyle, toFile);
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}

	@Override
	public boolean autoinclude() {
		return false;
	}
}
