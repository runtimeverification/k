package org.kframework.backend.maude;

import java.io.IOException;

import org.kframework.backend.Backend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.file.FileUtil;

public class MaudeBackend implements Backend {

	@Override
	public void run(Definition definition) throws IOException {
		MaudeFilter maudeFilter = new MaudeFilter();
		definition.accept(maudeFilter);

		String maudified = maudeFilter.getResult();

		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.maude", maudified);
	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}
}
