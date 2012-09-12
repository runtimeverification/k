package ro.uaic.info.fmse.krun;

import java.io.File;

import k.utils.XmlLoader;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.loader.CollectConsesVisitor;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.loader.UpdateReferencesVisitor;
import ro.uaic.info.fmse.transitions.labelify.KAppModifier;

public class KastParser {
	private static boolean initialized = false;

	public static void initParser() {
		File tbl = new File(K.kdir + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		k3parser.KParser.ImportTblPgm(tbl.getAbsolutePath());

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

		String parsed = k3parser.KParser.ParseProgramString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), pgm);
		XmlLoader.reportErrors(doc);
		XmlLoader.writeXmlFile(doc, K.kdir + "/pgm.xml");

		ASTNode out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());
		try {
			out = out.accept(new KAppModifier());
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		return out;
	}
}
