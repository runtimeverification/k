package k.utils;

import java.io.File;
import java.io.IOException;

import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.CollectConsesVisitor;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.loader.UpdateReferencesVisitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.utils.file.FileUtil;

public class ProgramLoader {

	public static ASTNode loadPgmAst2(File pgmFile, File dotk) throws IOException {
		File tbl = new File(dotk.getCanonicalPath() + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		k3parser.KParser.ImportTblPgm(tbl.getAbsolutePath());

		File f = pgmFile.getCanonicalFile();

		String content = FileUtil.getFileContent(f.getAbsolutePath());

		String parsed = k3parser.KParser.ParseProgramString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), pgmFile.getAbsolutePath());
		XmlLoader.reportErrors(doc);
		XmlLoader.writeXmlFile(doc, dotk.getAbsolutePath() + "/pgm.xml");

		ASTNode out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		return out;
	}

	/**
	 * Load program file to ASTNode.
	 * 
	 * Write pgm.xml cache in given dotk folder.
	 * 
	 * @param kappize
	 *            If true, then apply KAppModifier to AST.
	 */
	public static ASTNode loadPgmAst(File pgmFile, File dotk, Boolean kappize) throws IOException {
		File tbl = new File(dotk.getCanonicalPath() + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		k3parser.KParser.ImportTblPgm(tbl.getAbsolutePath());

		File f = pgmFile.getCanonicalFile();

		String content = FileUtil.getFileContent(f.getAbsolutePath());

		String parsed = k3parser.KParser.ParseProgramString(content);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), pgmFile.getAbsolutePath());
		XmlLoader.reportErrors(doc);
		XmlLoader.writeXmlFile(doc, dotk.getAbsolutePath() + "/pgm.xml");

		String definition = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def.xml");
		Document defDoc = ro.uaic.info.fmse.utils.xml.XML.getDocument(definition);
		ASTNode outDef = JavaClassesFactory.getTerm(defDoc.getDocumentElement());
		outDef.accept(new UpdateReferencesVisitor());
		outDef.accept(new CollectConsesVisitor());

		ASTNode out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		try {
			out = out.accept(new AmbFilter());
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		if (kappize)
			try {
				out = out.accept(new FlattenSyntax());
			} catch (TransformerException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}

		return out;
	}

	public static ASTNode loadPgmAst(File pgmFile, File dotk) throws IOException {
		return loadPgmAst(pgmFile, dotk, true);
	}

	/**
	 * Print maudified program to standard output.
	 * 
	 * Save it in dotk cache under pgm.maude.
	 */
	public static void processPgm(File pgmFile, File defFile) {
		try {
			// compile a definition here
			Stopwatch sw = new Stopwatch();

			File dotk = new File(defFile.getCanonicalFile().getParent() + "/.k");

			dotk.mkdirs();

			if (GlobalSettings.verbose)
				sw.printIntermediate("Importing Files = ");

			try {
				ASTNode out = loadPgmAst(pgmFile, dotk);
				if (GlobalSettings.verbose) {
					sw.printIntermediate("Parsing Program = ");
				}

				String kast = out.toMaude();

				System.out.println(kast);

				String language = FileUtil.stripExtension(defFile.getName());
				writeMaudifiedPgm(kast, language, dotk);

				if (GlobalSettings.verbose) {
					sw.printIntermediate("Maudify Program = ");
					sw.printTotal("Total           = ");
				}
			} catch (Exception e) {
				e.printStackTrace();
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse program: " + e.getLocalizedMessage(), pgmFile.getAbsolutePath(), "File system.", 0));
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}

	/**
	 * Store maudified AST of K program under `pgm.maude` in dotk directory. `pgm.maude` will also load language definition from `LANGUAGE-compiled.maude` in parent directory.
	 */
	private static void writeMaudifiedPgm(String kast, String language, File dotk) {
		String ast;
		ast = "load ../" + language + "-compiled.maude\n";
		ast += "set show command off .\n erewrite #eval(__((_|->_((# \"$PGM\"(.List{K})) , (\n\n";
		ast += kast;
		ast += "\n\n))),(.).Map))  .\n quit\n";

		FileUtil.saveInFile(dotk.getAbsolutePath() + "/pgm.maude", ast);
	}
}
