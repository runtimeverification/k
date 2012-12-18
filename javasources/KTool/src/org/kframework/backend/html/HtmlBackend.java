package org.kframework.backend.html;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class HtmlBackend extends BasicBackend {

	public HtmlBackend(Stopwatch sw) {
		super(sw);
	}

	@Override
	public void run(Definition definition) throws IOException {
		String fileSep = System.getProperty("file.separator");
		String htmlIncludePath = KPaths.getKBase(false) + fileSep + "include" + fileSep + "html" + fileSep;
		HTMLFilter htmlFilter = new HTMLFilter(htmlIncludePath);
		definition.accept(htmlFilter);

		String html = htmlFilter.getHTML();

		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.html", html);

		File canonicalFile = GlobalSettings.mainFile.getCanonicalFile();
		FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".html", html);
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}
}
