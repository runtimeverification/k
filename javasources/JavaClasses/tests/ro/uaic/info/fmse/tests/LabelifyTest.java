package ro.uaic.info.fmse.tests;

import static org.junit.Assert.assertTrue;

import java.util.Map;

import org.junit.Test;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.transitions.labelify.KAppFactory;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class LabelifyTest {

	@Test
	public void testGetTerm() {
		String file = "d:/work/dir cu spatii/k3/javasources/K3Syntax/test/imp/.k/def.xml";
		Document doc = XML.getDocument(FileUtil.readFileAsString(file));
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());

		file = "d:/work/dir cu spatii/k3/javasources/K3Syntax/test/imp/.k/pgm.xml";
		doc = XML.getDocument(FileUtil.readFileAsString(file));
		out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		ASTNode kapp = KAppFactory.getTerm(out);
		
		System.out.println(kapp.toMaude());

		assertTrue(doc != null);

		for (Map.Entry<String, Production> es : DefinitionHelper.conses.entrySet()) {
		//	System.out.println(es.getKey() + " -> " + es.getValue().getLabel());
		}
	}
}
