package org.kframework.backend.unparser;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class UnparserBackend extends BasicBackend {

	public UnparserBackend(Stopwatch sw, Context context) {
		super(sw, context);
	}

	@Override
	public void run(Definition definition) throws IOException {
		UnparserFilter unparserFilter = new UnparserFilter(context);
		definition.accept(unparserFilter);

		String unparsedText = unparserFilter.getResult();

		FileUtil.saveInFile(context.dotk.getAbsolutePath() + "/def.k", unparsedText);

		FileUtil.saveInFile(GlobalSettings.outputDir + File.separator + FileUtil.stripExtension(GlobalSettings.mainFile.getName()) + ".unparsed.k", unparsedText);
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}

}
