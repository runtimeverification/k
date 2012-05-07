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
import ro.uaic.info.fmse.transitions.labelify.KAppVisitor;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class LabelifyTest {

	@Test
	public void testGetTerm() {
		String file = "c:/work/k3/javasources/K3Syntax/test/imp/.k/def.xml";
		Document doc = XML.getDocument(FileUtil.readFileAsString(file));
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());

		file = "c:/work/k3/javasources/K3Syntax/test/imp/.k/pgm.xml";
		doc = XML.getDocument(FileUtil.readFileAsString(file));
		out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		KAppVisitor kapp = new KAppVisitor();
		out.accept(kapp);
		
		System.out.println(kapp.kappTerm.toMaude());

		assertTrue(doc != null);

		for (Map.Entry<String, Production> es : DefinitionHelper.conses.entrySet()) {
		//	System.out.println(es.getKey() + " -> " + es.getValue().getLabel());
		}
	}
}
