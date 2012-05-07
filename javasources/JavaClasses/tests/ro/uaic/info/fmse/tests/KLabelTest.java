package ro.uaic.info.fmse.tests;

import static org.junit.Assert.assertTrue;

import java.util.Map;

import org.junit.Test;
import org.w3c.dom.Document;

import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class KLabelTest {

	@Test
	public void testGetTerm() {
		String file = "c:/work/k3/javasources/K3Syntax/test/imp/.k/def.xml";
		Document doc = XML.getDocument(FileUtil.readFileAsString(file));
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());
		// System.out.println(out.toMaude());

		assertTrue(doc != null);

		for (Map.Entry<String, Production> es : DefinitionHelper.conses.entrySet()) {
			System.out.println(es.getKey() + " -> " + es.getValue().getLabel());
		}
	}
}
