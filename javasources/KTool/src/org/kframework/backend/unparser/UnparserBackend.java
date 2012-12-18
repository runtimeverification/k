package org.kframework.backend.unparser;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class UnparserBackend extends BasicBackend {

	public UnparserBackend(Stopwatch sw) {
		super(sw);
	}

	@Override
	public void run(Definition definition) throws IOException {
		UnparserFilter unparserFilter = new UnparserFilter();
		definition.accept(unparserFilter);

		String unparsedText = unparserFilter.getResult();

		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.k", unparsedText);

		File canonicalFile = GlobalSettings.mainFile.getCanonicalFile();
		FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".unparsed.k", unparsedText);
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}

}
