package k.utils;

import java.io.File;
import java.io.IOException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;

import ro.uaic.info.fmse.disambiguate.AmbFilter;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.loader.CollectConsesVisitor;
import ro.uaic.info.fmse.loader.JavaClassesFactory;
import ro.uaic.info.fmse.loader.UpdateReferencesVisitor;
import ro.uaic.info.fmse.transitions.labelify.KAppModifier;

public class ProgramLoader {
	public static void parsePgm(File mainFile, File defFile) {
		try {
			// compile a definition here
			Stopwatch sw = new Stopwatch();

			// for now just use this file as main argument
			File f = mainFile.getCanonicalFile();
			File dotk = new File(defFile.getCanonicalFile().getParent() + "/.k");

			dotk.mkdirs();
			File tbl = new File(dotk.getCanonicalPath() + "/pgm/Program.tbl");

			// ------------------------------------- import files in Stratego
			k3parser.KParser.ImportTblPgm(tbl.getAbsolutePath());
			if (GlobalSettings.verbose)
				sw.printIntermediate("Importing Files = ");

			try {
				String content = FileUtil.getFileContent(f.getAbsolutePath());

				String parsed = k3parser.KParser.ParseProgramString(content);
				Document doc = XmlLoader.getXMLDoc(parsed);

				XmlLoader.addFilename(doc.getFirstChild(), mainFile.getAbsolutePath());
				XmlLoader.reportErrors(doc);
				XmlLoader.writeXmlFile(doc, dotk.getAbsolutePath() + "/pgm.xml");

				if (GlobalSettings.verbose) {
					sw.printIntermediate("Parsing Program = ");
				}

				String definition = FileUtil.getFileContent(dotk.getAbsolutePath() + "/def.xml");

				Document defDoc = ro.uaic.info.fmse.utils.xml.XML.getDocument(definition);
				ASTNode outDef = JavaClassesFactory.getTerm(defDoc.getDocumentElement());
				outDef.accept(new UpdateReferencesVisitor());
				outDef.accept(new CollectConsesVisitor());

				ASTNode out = JavaClassesFactory.getTerm((Element) doc.getDocumentElement().getFirstChild().getNextSibling());

				out = out.accept(new AmbFilter());

				out = out.accept(new KAppModifier());
				String kast = out.toMaude();

				System.out.println(kast);

				String ast;
				ast = "load ../" + defFile.getName().substring(0, defFile.getName().length() - 2) + "-compiled.maude\n";
				ast += "set show command off .\n erewrite #eval(__((_|->_((# \"$PGM\"(.List{K})) , (\n\n";
				ast += kast;
				ast += "\n\n))),(.).Map))  .\n quit\n";

				FileUtil.saveInFile(dotk.getAbsolutePath() + "/pgm.maude", ast);

				if (GlobalSettings.verbose) {
					sw.printIntermediate("Maudify Program = ");
					sw.printTotal("Total           = ");
				}
			} catch (Exception e) {
				e.printStackTrace();
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Cannot parse program: " + e.getLocalizedMessage(), mainFile.getAbsolutePath(), "File system.", 0));
			}
		} catch (IOException e1) {
			e1.printStackTrace();
		}
	}
}
