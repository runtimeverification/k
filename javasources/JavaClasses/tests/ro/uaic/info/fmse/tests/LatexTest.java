package ro.uaic.info.fmse.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.w3c.dom.Document;

import ro.uaic.info.fmse.latex.LatexFilter;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class LatexTest {

	@Test
	public void testGetTerm() {
		String file = "d:/work/k3/javasources/K3Syntax/test/imp/.k/def.xml";
		Document doc = XML.getDocument(FileUtil.readFileAsString(file));
		assertTrue(doc != null);
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());

		out = new LatexFilter().visit(out);
	}
}
