package org.kframework.main;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Map;

import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.Configuration;
import org.kframework.kil.ConfigurationNotFound;
import org.kframework.kil.ConfigurationNotUnique;
import org.kframework.kil.Definition;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.loader.JavaClassesFactory;
import org.kframework.kil.Module;
import org.kframework.parser.DefinitionLoader;
import org.kframework.parser.concrete.KParser;
import org.kframework.utils.Error;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

public class KagregFrontEnd {

	public static void kagreg(String[] args) throws IOException, Exception {
		if (args.length != 2) {
			Error.report("There must be exactly two K definitions as arguments to kagreg.");
		}
		String firstDefinitionFileName = args[0];
		String secondDefinitionFileName = args[1];

		File firstDefinitionFile = new File(firstDefinitionFileName);
		File secondDefinitionFile = new File(secondDefinitionFileName);

		if (!firstDefinitionFile.exists()) {
			File errorFile = firstDefinitionFile;
			firstDefinitionFile = new File(firstDefinitionFileName + ".k");
			if (!firstDefinitionFile.exists()) {
				String msg = "File: " + errorFile.getName() + "(.k) not found.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, errorFile.getAbsolutePath(), "File system."));
			}
		}
		if (!secondDefinitionFile.exists()) {
			File errorFile = secondDefinitionFile;
			secondDefinitionFile = new File(secondDefinitionFileName + ".k");
			if (!secondDefinitionFile.exists()) {
				String msg = "File: " + errorFile.getName() + "(.k) not found.";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, errorFile.getAbsolutePath(), "File system."));
			}
		}
		
		GlobalSettings.verbose = true;

		String firstLang = FileUtil.getMainModule(firstDefinitionFile.getName());
		String secondLang = FileUtil.getMainModule(secondDefinitionFile.getName());
		
		DefinitionHelper definitionHelper1 = new DefinitionHelper();
		definitionHelper1.dotk = new File(firstDefinitionFile.getCanonicalFile().getParent() + File.separator + ".k");
		definitionHelper1.dotk.mkdirs();
		Definition firstDef = DefinitionLoader.loadDefinition(firstDefinitionFile, firstLang, true, definitionHelper1);
		
		GlobalSettings.synModule = null;
		KParser.reset();
		DefinitionHelper definitionHelper2 = new DefinitionHelper();
		assert definitionHelper2 != null;
		definitionHelper2.dotk = new File(secondDefinitionFile.getCanonicalFile().getParent() + File.separator + ".k");
		definitionHelper2.dotk.mkdirs();
		Definition secondDef = DefinitionLoader.loadDefinition(secondDefinitionFile, secondLang, true, definitionHelper2);

		Configuration firstConf = null;
		try {
			firstConf = firstDef.getSingletonConfiguration();
		} catch (ConfigurationNotUnique e) {
			System.err.println("Expecting a unique configuration in the first definition; found several.");
			return;
		} catch (ConfigurationNotFound e) {
			System.err.println("The first definition must have a configuration; found none.");
			return;
		}
		
		Configuration secondConf = null;
		try {
			secondConf = secondDef.getSingletonConfiguration();
		} catch (ConfigurationNotUnique e) {
			System.err.println("Expecting a unique configuration in the second definition; found several.");
			return;
		} catch (ConfigurationNotFound e) {
			System.err.println("The second definition must have a configuration; found none.");
			return;
		}

		String result = "";
		UnparserFilter unparserFirst = new UnparserFilter(definitionHelper1);
		unparserFirst.setForEquivalence();
		unparserFirst.visit(firstDef);
		result += unparserFirst.getResult();
		
		UnparserFilter unparserSecond = new UnparserFilter(definitionHelper2);
		unparserSecond.setForEquivalence();
		unparserSecond.visit(secondDef);
		result += unparserSecond.getResult();

		result += "\n\n\nconfiguration\n";
		result += "<agregation>\n";
		result += "<first>\n";
		UnparserFilter unparserFirstConfiguration = new UnparserFilter(definitionHelper1);
		firstConf.getBody().accept(unparserFirstConfiguration);
		result += unparserFirstConfiguration.getResult();
		result += "</first>\n\n\n";

		result += "<second>\n";
		UnparserFilter unparserSecondConfiguration = new UnparserFilter(definitionHelper2);
		secondConf.getBody().accept(unparserSecondConfiguration);
		result += unparserSecondConfiguration.getResult();
		result += "</second>\n\n\n";
		result += "</agregation>\n\n\n";

		BufferedWriter writer = new BufferedWriter(new FileWriter("result.k"));
		writer.write(result);
		writer.close();
	}
}
