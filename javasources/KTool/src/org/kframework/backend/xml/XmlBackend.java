package org.kframework.backend.xml;

import com.thoughtworks.xstream.XStream;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;

public class XmlBackend extends BasicBackend {

	public XmlBackend(Stopwatch sw) {
		super(sw);
	}

	@Override
	public void run(Definition definition) throws IOException {
//		definition = (org.kframework.kil.Definition)definition.accept(new AddEmptyLists());

		XStream xstream = new XStream();
		xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

		String xml = xstream.toXML(definition);

		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def.xml", xml);

		File canonicalFile = GlobalSettings.mainFile.getCanonicalFile();
		FileUtil.saveInFile(canonicalFile.getAbsolutePath().replaceFirst("\\.k$", "") + ".xml", xml);
	}

	@Override
	public String getDefaultStep() {
		return "FirstStep";
	}

}
