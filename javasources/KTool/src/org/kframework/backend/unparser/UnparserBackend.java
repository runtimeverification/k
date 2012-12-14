package org.kframework.backend.unparser;

import java.io.File;
import java.io.IOException;

import org.kframework.backend.Backend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

public class UnparserBackend implements Backend {

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
