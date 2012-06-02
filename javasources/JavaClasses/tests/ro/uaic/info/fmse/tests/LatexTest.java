package ro.uaic.info.fmse.tests;

import static org.junit.Assert.assertTrue;

import org.junit.Test;
import org.w3c.dom.Document;

import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.latex.LatexFilter;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class LatexTest {

	@Test
	public void testGetTerm() {
		String file = "/Users/tserban2/Documents/k/trunk/dist/examples/imp/.k/def.xml";
		Document doc = XML.getDocument(FileUtil.readFileAsString(file));
		assertTrue(doc != null);
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());
		LatexFilter filter = new LatexFilter(); 
		out.accept(filter);
		String endl = System.getProperty("line.separator");
		System.out.println("\\documentclass{article}" + endl 
				+ "\\usepackage[poster,style=bubble]{/Users/tserban2/Documents/k/branches/k2/core/latex/k}" + endl
				+ "\\setlength{\\parindent}{1em}" + endl
				+ "\\title{IMP}" + endl
				+ "\\author{Grigore Ro\\c{s}u (\\texttt{grosu@illinois.edu})}" + endl
				+ "\\organization{University of Illinois at Urbana-Champaign}" + endl
				+ "\\begin{document}" + endl
				+ filter.getResult()
				+ "\\end{document}" + endl);
	}
}
