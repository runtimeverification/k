package org.kframework.backend.symbolic;

import java.io.IOException;

import org.kframework.backend.Backend;
import org.kframework.backend.BasicBackend;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;

import com.thoughtworks.xstream.XStream;

public class SymbolicBackend extends BasicBackend implements Backend {

	public SymbolicBackend(Stopwatch sw) {
		super(sw);
		// TODO Auto-generated constructor stub
	}

	@Override
	public void run(Definition definition) throws IOException {

		try {
			SymbolicTransformer st = new SymbolicTransformer("");
			Definition def = (Definition) st.transform(definition);
			
			UnparserFilter unparserFilter = new UnparserFilter();
			def.accept(unparserFilter);

			String unparsedText = unparserFilter.getResult();
			
			System.out.println(unparsedText);
			
			XStream xstream = new XStream();
			xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

			String xml = xstream.toXML(def);

			FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/def-symbolic.xml", xml);

//			File canonicalFile = GlobalSettings.mainFile.getCanonicalFile();
//			FileUtil.saveInFile(canonicalFile.getAbsolutePath().replaceFirst("\\.k$", "") + ".xml", xml);

		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}
}
