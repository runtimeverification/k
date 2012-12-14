package org.kframework.backend.xml;

import java.io.File;
import java.io.IOException;

import org.kframework.backend.Backend;
import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import com.thoughtworks.xstream.XStream;

public class XmlBackend implements Backend {

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
