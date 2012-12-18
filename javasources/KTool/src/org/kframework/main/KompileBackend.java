package org.kframework.main;

import org.kframework.backend.BasicBackend;
import org.kframework.backend.maude.MaudeBackend;
import org.kframework.backend.maude.MaudeBuiltinsFilter;
import org.kframework.backend.maude.MaudeRuleExtractor;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.KPaths;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.maude.MaudeRun;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.List;
import java.util.Properties;

public class KompileBackend extends BasicBackend {

	private static String metadataTags(List<String> tags) {
		String result = "";
		for (String s : tags) {
			result += s + "=()";
		}
		return "\"" + result + "\"";
	}

	public KompileBackend(Stopwatch sw) {
		super(sw);
	}

	@Override
	public Definition lastStep(Definition def) {
		MaudeRuleExtractor ruleExtractor = new MaudeRuleExtractor();
		try {
			def = (Definition) def.accept(ruleExtractor);
		} catch (TransformerException e) {
		}
		final String mainModule = def.getMainModule();
		String rules = "mod " + mainModule + "-RULES is\n" + " including " + mainModule + "-BASE .\n" + ruleExtractor.getResult() + "endm\n";
		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/rules.maude", rules);
		if (GlobalSettings.verbose)
			sw.printIntermediate("Writing the compiled rules.");
		return def;
	}

	@Override
	public Definition firstStep(Definition javaDef) {
		String fileSep = System.getProperty("file.separator");
		String includePath = KPaths.getKBase(false) + fileSep + "include" + fileSep + "maude" + fileSep;
		Properties builtinsProperties = new Properties();
		try {
			builtinsProperties.load(new FileInputStream(includePath + "hooks.properties"));
		} catch (IOException e) {
			e.printStackTrace();
		}
		MaudeBuiltinsFilter builtinsFilter = new MaudeBuiltinsFilter(builtinsProperties);
		javaDef.accept(builtinsFilter);
		final String mainModule = javaDef.getMainModule();
		String builtins = "mod " + mainModule + "-BUILTINS is\n" + " including " + mainModule + "-BASE .\n" + builtinsFilter.getResult() + "endm\n";
		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/builtins.maude", builtins);
		if (GlobalSettings.verbose)
			sw.printIntermediate("Generating equations for Hooks.");
		return super.firstStep(javaDef);
	}

	@Override
	public void run(Definition javaDef) throws IOException {
		new MaudeBackend(sw).run(javaDef);

		String load = "load \"" + KPaths.getKBase(true) + "/bin/maude/lib/k-prelude\"\n";
		String definition = "load \"" + KPaths.windowfyPath(DefinitionHelper.dotk.getAbsolutePath() + "/def.maude") + "\"\n";

		// load libraries if any
		String maudeLib = GlobalSettings.lib.equals("") ? "" : "load " + KPaths.windowfyPath(new File(GlobalSettings.lib).getAbsolutePath()) + "\n";
		load += maudeLib;

		String transition = metadataTags(GlobalSettings.transition);
		String superheat = metadataTags(GlobalSettings.superheat);
		String supercool = metadataTags(GlobalSettings.supercool);

		String step = "RESOLVE-HOOKS";
		final String mainModule = javaDef.getMainModule();
		String compile = load
				+ definition
				// + maudeFilter.getResult()
				+ " load \"" + KPaths.getKBase(true) + "/bin/maude/compiler/all-tools\"\n" + "---(\n" + "rew in COMPILE-ONESHOT : partialCompile('" + mainModule + ", '" + step + ") .\n" + "quit\n"
				+ "---)\n" + " loop compile .\n" + "(compile " + mainModule + " " + step + " transitions " + transition + " superheats " + superheat + " supercools " + supercool
				+ " anywheres \"anywhere=() function=() predicate=() macro=()\" " + "defineds \"function=() predicate=() defined=()\" .)\n" + "quit\n";

		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/compile.maude", compile);

		// call maude to kompile the definition
		String compiled = MaudeRun.run_maude(DefinitionHelper.dotk.getAbsoluteFile(), compile);

		int start = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-BEGIN---") + "---K-MAUDE-GENERATED-OUTPUT-BEGIN---".length();
		int enddd = compiled.indexOf("---K-MAUDE-GENERATED-OUTPUT-END-----");
		compiled = compiled.substring(start, enddd).replaceFirst(mainModule, mainModule + "-BASE");

		String defFile = javaDef.getMainFile().replaceFirst("\\.[a-zA-Z]+$", "");
		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/base.maude", compiled);

		if (GlobalSettings.verbose)
			sw.printIntermediate("Running Maude");

		String main = load + "load \".k/base.maude\"\n" + "load \".k/builtins.maude\"\n" + "load \".k/rules.maude\"\n" + "mod " + mainModule + " is \n" + "  including " + mainModule + "-BASE .\n"
				+ "  including " + mainModule + "-BUILTINS .\n" + "  including " + mainModule + "-RULES .\n" + "endm\n";
		FileUtil.saveInFile(defFile + "-compiled.maude", main);

		if (start == -1 || enddd == -1) {
			KException exception = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, "Incomplete output generated by the compiler. Check the '" + defFile + "-compiled.maude'.",
					"top level", "Maude compilation");
			GlobalSettings.kem.register(exception);
		}
	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}

}
