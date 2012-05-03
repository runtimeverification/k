package ro.uaic.info.fmse.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.w3c.dom.Document;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class LoadDefinitionTest {

	@Test
	public void testGetTerm() {
		String file = "/home/andrei.arusoaie/work/k3/javasources/K3Syntax/test/simple-untyped/.k/def.xml";
		Document doc = XML.getDocument(FileUtil.readFileAsString(file));
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());
		System.out.println(out);
		
		assertTrue(doc != null);
	}

}
