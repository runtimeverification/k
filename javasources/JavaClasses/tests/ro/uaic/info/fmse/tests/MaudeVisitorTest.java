package ro.uaic.info.fmse.tests;

import static org.junit.Assert.*;

import org.junit.Test;
import org.w3c.dom.Document;

import ro.uaic.info.fmse.latex.LatexFilter;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.parsing.ASTNode;
import ro.uaic.info.fmse.transitions.maude.MaudeVisitor;
import ro.uaic.info.fmse.utils.file.FileUtil;
import ro.uaic.info.fmse.utils.xml.XML;

public class MaudeVisitorTest {

	@Test
	public void testVisitDefinition() {
		String file = "/home/andrei.arusoaie/work/trunk/dist/examples/cink-basic/.k/def.xml";
		Document doc = XML.getDocument(FileUtil.readFileAsString(file));
		assertTrue(doc != null);
		ASTNode out = JavaClassesFactory.getTerm(doc.getDocumentElement());
		LatexFilter filter = new LatexFilter(); 
		out.accept(filter);
		
		MaudeVisitor mv = new MaudeVisitor();
		mv.visit(out);
		
		System.out.println(mv.getMaudified());
	}

}
