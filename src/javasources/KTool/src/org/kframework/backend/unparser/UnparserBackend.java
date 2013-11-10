package org.kframework.backend.unparser;

import org.apache.commons.io.FilenameUtils;
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

		FileUtil.save(context.dotk.getAbsolutePath() + "/def.k", unparsedText);

        FileUtil.save(GlobalSettings.outputDir + File.separator + FilenameUtils.removeExtension(GlobalSettings.mainFile.getName()) + ".unparsed.k", unparsedText);
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}

}
