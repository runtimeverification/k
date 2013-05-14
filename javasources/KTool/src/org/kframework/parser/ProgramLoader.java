package org.kframework.parser;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;

import org.kframework.compile.transformers.AddEmptyLists;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.transformers.RemoveBrackets;
import org.kframework.compile.transformers.RemoveSyntacticCasts;
import org.kframework.compile.utils.CompilerStepDone;
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
import org.kframework.utils.BinaryLoader;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.XmlLoader;
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
	public static ASTNode loadPgmAst(String content, String filename, Boolean kappize, String startSymbol, DefinitionHelper definitionHelper) throws IOException, TransformerException {
		File tbl = new File(definitionHelper.kompiled.getCanonicalPath() + "/pgm/Program.tbl");

		// ------------------------------------- import files in Stratego
		org.kframework.parser.concrete.KParser.ImportTblPgm(tbl.getAbsolutePath());
		String parsed = org.kframework.parser.concrete.KParser.ParseProgramString(content, startSymbol);
		Document doc = XmlLoader.getXMLDoc(parsed);

		XmlLoader.addFilename(doc.getFirstChild(), filename);
		XmlLoader.reportErrors(doc);
		FileUtil.saveInFile(definitionHelper.kompiled.getAbsolutePath() + "/pgm.xml", parsed);
		ASTNode out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

		out = out.accept(new PriorityFilter(definitionHelper));
		out = out.accept(new PreferAvoidFilter(definitionHelper));
		out = out.accept(new AmbFilter(definitionHelper));
		out = out.accept(new RemoveBrackets(definitionHelper));

		if (kappize)
			out = out.accept(new FlattenSyntax(definitionHelper));

		return out;
	}

	public static ASTNode loadPgmAst(String content, String filename, String startSymbol, DefinitionHelper definitionHelper) throws IOException, TransformerException {
		return loadPgmAst(content, filename, true, startSymbol, definitionHelper);
	}

	public static ASTNode loadPgmAst(File pgmFile, boolean kappize, String startSymbol, DefinitionHelper definitionHelper) throws IOException, TransformerException {
		String filename = pgmFile.getCanonicalFile().getAbsolutePath();
		String content = FileUtil.getFileContent(filename);
		return loadPgmAst(content, filename, kappize, startSymbol, definitionHelper);
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
	public static Term processPgm(String content, String filename, Definition def, String startSymbol, DefinitionHelper definitionHelper) throws TransformerException {
		// compile a definition here
		Stopwatch sw = new Stopwatch();

		if (GlobalSettings.verbose)
			sw.printIntermediate("Importing Files");

		try {
			ASTNode out;
			if (GlobalSettings.whatParser == GlobalSettings.ParserType.GROUND) {
				org.kframework.parser.concrete.KParser.ImportTblGround(definitionHelper.kompiled.getCanonicalPath() + "/ground/Concrete.tbl");
				out = DefinitionLoader.parseCmdString(content, "", filename, definitionHelper);
				out = out.accept(new RemoveBrackets(definitionHelper));
				out = out.accept(new AddEmptyLists(definitionHelper));
				out = out.accept(new RemoveSyntacticCasts(definitionHelper));
				out = out.accept(new FlattenSyntax(definitionHelper));
				out = out.accept(new RemoveSyntacticCasts(definitionHelper));
			} else if (GlobalSettings.whatParser == GlobalSettings.ParserType.RULES) {
				org.kframework.parser.concrete.KParser.ImportTbl(definitionHelper.kompiled.getCanonicalPath() + "/def/Concrete.tbl");
				out = DefinitionLoader.parsePattern(content, filename, definitionHelper);
				try {
					out = new RuleCompilerSteps(def, definitionHelper).compile((Rule) out, null);
				} catch (CompilerStepDone e) {
					out = (ASTNode) e.getResult();
				}
				out = ((Rule) out).getBody();
			} else if (GlobalSettings.whatParser == GlobalSettings.ParserType.BINARY) {
				out = (org.kframework.kil.Cell) BinaryLoader.fromBinary(new FileInputStream(filename));
			} else {
				out = loadPgmAst(content, filename, startSymbol, definitionHelper);
			}
			if (GlobalSettings.verbose) {
				sw.printIntermediate("Parsing Program");
			}

			return (Term) out;
		} catch (IOException e) {
			throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse program: " + e.getLocalizedMessage(), filename, "File system."));
		}
	}
}
