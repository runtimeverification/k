package org.kframework.utils;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.concrete.disambiguate.AmbFilter;
import org.kframework.parser.concrete.disambiguate.PreferAvoidFilter;
import org.kframework.parser.concrete.disambiguate.PriorityFilter;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;
import org.w3c.dom.Document;
import org.w3c.dom.Element;

public class ProgramLoader {

	/**
	 * Load program file to ASTNode.
	 * 
	 * Write pgm.xml cache in given dotk folder.
	 * 
	 * @param kappize
	 *            If true, then apply KAppModifier to AST.
	 */
	public static ASTNode loadPgmAst(String content, String filename, Boolean kappize, String startSymbol) throws IOException {
		File tbl = new File(DefinitionHelper.kompiled.getCanonicalPath() + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		org.kframework.parser.concrete.KParser.ImportTblPgm(tbl.getAbsolutePath());
		String parsed = org.kframework.parser.concrete.KParser.ParseProgramString(content, startSymbol);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(DefinitionHelper.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		ASTNode out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		try {
			out = out.accept(new PriorityFilter());
			out = out.accept(new PreferAvoidFilter());
			out = out.accept(new AmbFilter());
			out = out.accept(new RemoveBrackets());
		} catch (TransformerException e) {
			e.printStackTrace();
		}

		if (kappize)
			try {
				out = out.accept(new FlattenSyntax());
			} catch (TransformerException e) {
				e.printStackTrace();
			}

		return out;
	}

	public static ASTNode loadPgmAst(String content, String filename, String startSymbol) throws IOException {
		return loadPgmAst(content, filename, true, startSymbol);
	}

	public static ASTNode loadPgmAst(File pgmFile, boolean kappize, String startSymbol) throws IOException {
		String filename = pgmFile.getCanonicalFile().getAbsolutePath();
		String content = FileUtil.getFileContent(filename);
		return loadPgmAst(content, filename, kappize, startSymbol);
	}

	/**
	 * Print maudified program to standard output.
	 * 
	 * Save it in kompiled cache under pgm.maude.
	 * 
	 * @param indentationOptions
	 * @param prettyPrint
	 * @param nextline
	 */
	public static Term processPgm(String content, String filename, Definition def, String startSymbol) {
		// compile a definition here
		Stopwatch sw = new Stopwatch();

		if (GlobalSettings.verbose)
			sw.printIntermediate("Importing Files");

		try {
			ASTNode out;
			if (GlobalSettings.whatParser == GlobalSettings.ParserType.GROUND) {
				org.kframework.parser.concrete.KParser.ImportTblGround(DefinitionHelper.kompiled.getCanonicalPath() + "/ground/Concrete.tbl");
				out = DefinitionLoader.parseCmdString(content, "", filename);
				out = out.accept(new AddEmptyLists());
				out = out.accept(new FlattenSyntax());
			} else if (GlobalSettings.whatParser == GlobalSettings.ParserType.RULES) {
				org.kframework.parser.concrete.KParser.ImportTbl(DefinitionHelper.kompiled.getCanonicalPath() + "/def/Concrete.tbl");
				out = DefinitionLoader.parsePattern(content, filename);
				out = new RuleCompilerSteps(def).compile((Rule) out, null);
				out = ((Rule) out).getBody();
			} else if (GlobalSettings.whatParser == GlobalSettings.ParserType.BINARY) {
				out = (org.kframework.kil.Cell) BinaryLoader.fromBinary(new FileInputStream(filename));
			} else {
				out = loadPgmAst(content, filename, startSymbol);
			}
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Parsing Program");
			}

			return (Term) out;
		} catch (Exception e) {
			e.printStackTrace();
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse program: " + e.getLocalizedMessage(), filename, "File system."));
			return null;
		}
	}
}
