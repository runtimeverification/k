package org.kframework.krun;

import java.io.File;


import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.CollectConsesVisitor;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.UpdateReferencesVisitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.XmlLoader;
import org.w3c.dom.Document;
import org.w3c.dom.Element;


public class KastParser {
	private static boolean initialized = false;

	public static void initParser() {
		File tbl = new File(K.kdir + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		org.kframework.parser.concrete.KParser.ImportTblPgm(tbl.getAbsolutePath());

		String definition = FileUtil.getFileContent(K.kdir + "/def.xml");
		Document defDoc = ro.uaic.info.fmse.utils.xml.XML.getDocument(definition);
		ASTNode outDef = JavaClassesFactory.getTerm(defDoc.getDocumentElement());
		outDef.accept(new UpdateReferencesVisitor());
		outDef.accept(new CollectConsesVisitor());

		initialized = true;
		// TODO: save outDef somewhere - maybe you will need it later
	}

	public static String getKAST(String pgm) {
		ASTNode out = getKastTerm(pgm);

		return out.toMaude();
	}

	public static ASTNode getKastTerm(String pgm) {
		if (!initialized)
			initParser();

		File f = new File(pgm);

		String content = FileUtil.getFileContent(f.getAbsolutePath());

		String parsed = org.kframework.parser.concrete.KParser.ParseProgramString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), pgm);
		XmlLoader.reportErrors(doc);
		XmlLoader.writeXmlFile(doc, K.kdir + "/pgm.xml");

		ASTNode out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
		try {
			out = out.accept(new FlattenSyntax());
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		return out;
	}
}
