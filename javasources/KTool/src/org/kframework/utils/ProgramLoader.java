package org.kframework.utils;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.backend.unparser.IndentationOptions;
import org.kframework.backend.unparser.KastFilter;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

import java.io.File;
import java.io.IOException;

public class ProgramLoader {

	/**
	 * Load program file to ASTNode.
	 * 
	 * Write pgm.xml cache in given dotk folder.
	 * 
	 * @param kappize
	 *            If true, then apply KAppModifier to AST.
	 */
	public static ASTNode loadPgmAst(String content, String filename, Boolean kappize) throws IOException {
		File tbl = new File(DefinitionHelper.dotk.getCanonicalPath() + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		org.kframework.parser.concrete.KParser.ImportTblPgm(tbl.getAbsolutePath());
		String parsed = org.kframework.parser.concrete.KParser.ParseProgramString(content, DefinitionHelper.startSymbolPgm);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		XmlLoader.writeXmlFile(doc, DefinitionHelper.dotk.getAbsolutePath() + "/pgm.xml");
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

	public static ASTNode loadPgmAst(String content, String filename) throws IOException {
		return loadPgmAst(content, filename, true);
	}

	public static ASTNode loadPgmAst(File pgmFile, boolean kappize) throws IOException {
		String filename = pgmFile.getCanonicalFile().getAbsolutePath();
		String content = FileUtil.getFileContent(filename);
		return loadPgmAst(content, filename, kappize);
	}

	/**
	 * Print maudified program to standard output.
	 * 
	 * Save it in dotk cache under pgm.maude.
	 * 
	 * @param indentationOptions
	 * @param prettyPrint
	 * @param nextline
	 */
	public static void processPgm(String content, String filename, Definition def, boolean prettyPrint, boolean nextline, IndentationOptions indentationOptions, boolean useDefParser) {
		// compile a definition here
		Stopwatch sw = new Stopwatch();

		if (GlobalSettings.verbose)
			sw.printIntermediate("Importing Files");

		try {
			ASTNode out;
			if (useDefParser) {
				org.kframework.parser.concrete.KParser.ImportTbl(DefinitionHelper.dotk.getCanonicalPath() + "/def/Concrete.tbl");
				out = DefinitionLoader.parseCmdString(content, "");
				out = out.accept(new FlattenSyntax());
				out = MetaK.kWrapper((Term) out);
			} else {
				out = loadPgmAst(content, filename);
			}
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Parsing Program");
			}

			String kast;
			if (prettyPrint) {
				KastFilter kastFilter = new KastFilter(indentationOptions, nextline);
				out.accept(kastFilter);
				kast = kastFilter.getResult();
			} else {
				MaudeFilter maudeFilter = new MaudeFilter();
				out.accept(maudeFilter);
				kast = maudeFilter.getResult();
			}

			System.out.println(kast);

			String language = FileUtil.stripExtension(def.getMainFile());
			writeMaudifiedPgm(kast, language, DefinitionHelper.dotk);

			if (GlobalSettings.verbose) {
				sw.printIntermediate("Maudify Program");
				sw.printTotal("Total");
			}
		} catch (Exception e) {
			e.printStackTrace();
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse program: " + e.getLocalizedMessage(), filename, "File system."));
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
