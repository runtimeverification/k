package ro.uaic.info.fmse.pp.tests;

//import org.junit.Test;
import org.w3c.dom.Document;

import ro.uaic.info.fmse.pp.labels.LabelGenerator;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;
import ro.uaic.info.fmse.utils.xml.XmlFormatter;

public class LabelGeneratorTest {

	//@Test
	public void testGenerateKLabels() {
		
		String xmlFile = "/home/andrei.arusoaie/work/k3/javasources/K3Syntax/test/simple-untyped/.k/def.xml";
		String desktopFile = "/home/andrei.arusoaie/Desktop/tmp.xml";
		
		Document kilDoc = XML.getDocument(FileUtil.readFileAsString(xmlFile));
		LabelGenerator lg = new LabelGenerator();
		kilDoc = lg.generateKLabels(kilDoc);
		
		FileUtil.saveInFile(desktopFile, XmlFormatter.format(kilDoc));
	}

}
