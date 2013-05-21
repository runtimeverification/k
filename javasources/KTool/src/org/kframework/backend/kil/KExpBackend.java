package org.kframework.backend.kil;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class KExpBackend extends BasicBackend {

	public KExpBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

	@Override
	public void run(Definition definition) throws IOException {
		KExpFilter unparserFilter = new KExpFilter(context);
		definition.accept(unparserFilter);

		String kexpText = unparserFilter.getResult();

		FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/def.kexp", kexpText);

		File canonicalFile = GlobalSettings.mainFile.getCanonicalFile();
		FileUtil.saveInFile(FileUtil.stripExtension(canonicalFile.getAbsolutePath()) + ".kexp", kexpText);
	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}

}
