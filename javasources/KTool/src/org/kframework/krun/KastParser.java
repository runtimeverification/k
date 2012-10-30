package org.kframework.krun;

import java.io.File;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.utils.XmlLoader;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import com.thoughtworks.xstream.XStream;

public class KastParser {
	private static boolean initialized = false;

	public static void initParser() {
		File tbl = new File(K.kdir + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		org.kframework.parser.concrete.KParser.ImportTblPgm(tbl.getAbsolutePath());

		XStream xstream = new XStream();
		xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

		org.kframework.kil.Definition javaDef = (org.kframework.kil.Definition) xstream.fromXML(new File(K.kdir + "/defx.xml"));
		// This is essential for generating maude
		javaDef.preprocess();

		initialized = true;
		// TODO: save outDef somewhere - maybe you will need it later
	}

	public static String getKAST(String pgm) {
		ASTNode out = getKastTerm(pgm);

		MaudeFilter maudeFilter = new MaudeFilter();
		out.accept(maudeFilter);
		return maudeFilter.getResult();
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
			out = out.accept(new AmbFilter());
			out = out.accept(new FlattenSyntax());
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		return out;
	}
}
