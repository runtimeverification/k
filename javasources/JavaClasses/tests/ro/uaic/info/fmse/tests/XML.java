package ro.uaic.info.fmse.tests;

import static org.junit.Assert.assertTrue;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.junit.Test;
import org.w3c.dom.Document;

import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.utils.file.FileUtil;

public class XML {

	@Test
	public void testToXml() throws ParserConfigurationException {
		String file = "/home/andrei.arusoaie/work/k3/javasources/K3Syntax/test/simple-untyped/.k/def.xml";
		Document doc = ro.uaic.info.fmse.utils.xml.XML.getDocument(FileUtil.readFileAsString(file));
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());
		
		//We need a Document
        DocumentBuilderFactory dbfac = DocumentBuilderFactory.newInstance();
        DocumentBuilder docBuilder = dbfac.newDocumentBuilder();
        Document docx = docBuilder.newDocument();
        docx.appendChild(out.toXml(docx));
        
        FileUtil.saveInFile("/home/andrei.arusoaie/Desktop/myXml.xml", ro.uaic.info.fmse.utils.xml.XmlFormatter.format(docx));
		
		assertTrue(out != null);
	}

}
