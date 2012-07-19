package ro.uaic.info.fmse.jkrun;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import ro.uaic.info.fmse.runner.KRunner;

import org.fusesource.jansi.AnsiConsole;

public class Main {

	private static final String USAGE = "krun [options] <file>" + K.lineSeparator;
	private static final String HEADER = "";
	private static final String FOOTER = "";

	public static void printUsage(Options options) {
		HelpFormatter helpFormatter = new HelpFormatter();
		helpFormatter.setOptionComparator(new CommandlineOptions.OptionComparator());
		helpFormatter.setWidth(100);
		helpFormatter.printHelp(USAGE, HEADER, options, FOOTER);
		System.out.println();
	}

	public static void printVersion() {
		System.out.println("JKrun 0.2.0\n" + "Copyright (C) 2012 Necula Emilian & Raluca");
	}

	public static void printStatistics(CommandLine cmd) {
		PrettyPrintOutput p = new PrettyPrintOutput(cmd);
		File file = new File(K.maude_output);
		if ("search".equals(K.maude_cmd) || p.getCmd().hasOption("xsearch-pattern")) {
			String totalStates = p.getSearchTagAttr(file, "total-states");
			String totalRewrites = p.getSearchTagAttr(file, "total-rewrites");
			String realTime = p.getSearchTagAttr(file, "real-time-ms");
			String cpuTime = p.getSearchTagAttr(file, "cpu-time-ms");
			String rewritesPerSecond = p.getSearchTagAttr(file, "rewrites-per-second");
			AnsiConsole.out.println(PrettyPrintOutput.ANSI_BLUE + "states: " + totalStates + " rewrites: " + totalRewrites + " in " + cpuTime + "ms cpu (" + realTime + "ms real) (" + rewritesPerSecond + " rewrites/second)" + PrettyPrintOutput.ANSI_NORMAL);
		} else if ("erewrite".equals(K.maude_cmd)){
			String totalRewrites = p.getResultTagAttr(file, "total-rewrites");
			String realTime = p.getResultTagAttr(file, "real-time-ms");
			String cpuTime = p.getResultTagAttr(file, "cpu-time-ms");
			String rewritesPerSecond = p.getResultTagAttr(file, "rewrites-per-second");
			AnsiConsole.out.println(PrettyPrintOutput.ANSI_BLUE + "rewrites: " + totalRewrites + " in " + cpuTime + "ms cpu (" + realTime + "ms real) (" + rewritesPerSecond + " rewrites/second)" + PrettyPrintOutput.ANSI_NORMAL);
		}
	}

	public static void printSearchResults() {
		PrettyPrintOutput p = new PrettyPrintOutput();
		File file = new File(K.maude_output);
		String solutionNumber = p.getSearchTagAttr(file, "solution-number");
		String stateNumber = p.getSearchTagAttr(file, "state-number");
		if (!solutionNumber.equals("NONE")) {
			System.out.println("Search results:\n");
			AnsiConsole.out.println(PrettyPrintOutput.ANSI_BLUE + "Solution " + solutionNumber + ", state " + stateNumber + ":" + PrettyPrintOutput.ANSI_NORMAL);
		}
		else {
			System.out.println("Found no solution");
		}
	}

	public static String initOptions(String path, String lang) {
		String result = null;
		String path_ = null;
		String fileName = null;
		String compiledDef = null; 
		StringBuilder str = new StringBuilder();
		int count = 0;

		try {
			ArrayList<File> maudeFiles = FileUtil.searchFiles(path, "maude", false);
			for (File maudeFile : maudeFiles) {
				String fullPath = maudeFile.getCanonicalPath();
				path_ = FileUtil.dropExtension(fullPath, ".", K.fileSeparator);
				compiledDef = maudeFile.getName();
				int sep = path_.lastIndexOf(K.fileSeparator);
				fileName = path_.substring(sep + 1);
				if (fileName.startsWith(lang) && lang.length() > 0) {
					result = fullPath;
					str.append("\"./" + fileName + "\" ");
					count++;
				}
			    if (lang.length() == 0 && fileName.endsWith("-compiled")) {
			    	count++;
			    }
			}
			if (count > 1) {
				Error.report("\nMultiple compiled definitions found.\nPlease use only one of: " + str.toString());
			} else if (maudeFiles.size() == 1) {
				result = compiledDef; 
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return result;
	}

	public static void resolveOption(String optionName, String lang, CommandLine cmd) {
		String s = FileUtil.dropKExtension(K.k_definition, ".", K.fileSeparator);
		int sep = s.lastIndexOf(K.fileSeparator);
		String str = s.substring(sep + 1).toUpperCase();
		int index;

		if (optionName == "compiled-def") {
			if (cmd.hasOption("k-definition")) {
				K.compiled_def = s + "-compiled.maude";
			} else {
				K.compiled_def = initOptions(K.userdir, lang);
				if (K.compiled_def != null) {
					index = K.compiled_def.indexOf("-compiled.maude");
					K.k_definition = K.compiled_def.substring(0, index);
				}
			}
		} else if (optionName == "main-module") {
			K.main_module = str;
		} else if (optionName == "syntax-module") {
			K.syntax_module = str + "-SYNTAX";
		}
	}

	/**
	 * @param cmds
	 *            represents the arguments/options given to jkrun command..
	 */
	public static void execute_Krun(String cmds[]) {
		//delete temporary krun directory
		FileUtil.deleteDirectory(new File(K.krunDir));
		
		CommandlineOptions cmd_options = new CommandlineOptions();
		CommandLine cmd = cmd_options.parse(cmds);
		try {
		
			// Parse the program arguments

			if (cmd.hasOption("search")) {
				K.maude_cmd = "search";
				K.io = false;
				K.do_search = true;
				K.output_mode = "pretty";
			}
			if (cmd.hasOption("config")) {
				K.output_mode = "pretty";
			}
			if (cmd.hasOption("no-config")) {
				K.output_mode = "none";
			}
			if (cmd.hasOption('h') || cmd.hasOption('?')) {
				K.help = true;
			}
			if (cmd.hasOption('v')) {
				K.version = true;
			}
			if (cmd.hasOption("k-definition")) {
				K.k_definition = new File(cmd.getOptionValue("k-definition")).getCanonicalPath();
			}
			if (cmd.hasOption("main-module")) {
				K.main_module = cmd.getOptionValue("main-module");
			}
			if (cmd.hasOption("syntax-module")) {
				K.syntax_module = cmd.getOptionValue("syntax-module");
			}
			if (cmd.hasOption("parser")) {
				K.parser = cmd.getOptionValue("parser");
			}
			if (cmd.hasOption("io")) {
				K.io = true;
			}
			if (cmd.hasOption("no-io")) {
				K.io = false;
			}
			if (cmd.hasOption("statistics")) {
				K.statistics = true;
			}
			if (cmd.hasOption("no-statistics")) {
				K.statistics = false;
			}
			if (cmd.hasOption("color")) {
				K.color = true;
			}
			if (cmd.hasOption("no-color")) {
				K.color = false;
			}
			if (cmd.hasOption("parens")) {
				K.parens = true;
			}
			if (cmd.hasOption("no-parens")) {
				K.parens = false;
			}
			if (cmd.hasOption("compiled-def")) {
				K.compiled_def = new File(cmd.getOptionValue("compiled-def")).getCanonicalPath();
			}
			if (cmd.hasOption("do-search")) {
				K.do_search = true;
			}
			if (cmd.hasOption("no-do-search")) {
				K.do_search = false;
			}
			if (cmd.hasOption("maude-cmd")) {
				K.maude_cmd = cmd.getOptionValue("maude-cmd");
			}
			if (cmd.hasOption("xsearch-pattern")) {
				K.xsearch_pattern = cmd.getOptionValue("xsearch-pattern");
				//System.out.println("xsearch-pattern:" + K.xsearch_pattern);
			}
			if (cmd.hasOption("output-mode")) {
				K.output_mode = cmd.getOptionValue("output-mode");
			}
			if (cmd.hasOption("log-io")) {
				K.log_io = true;
			}
			if (cmd.hasOption("no-log-io")) {
				K.log_io = false;
			}
			if (cmd.hasOption("debug")) {
				K.debug = true;
			}
			if (cmd.hasOption("trace")) {
				K.trace = true;
			}
			if (cmd.hasOption("pgm")) {
				K.pgm = new File(cmd.getOptionValue("pgm")).getCanonicalPath();
			}
			if (cmd.hasOption("ltlmc")) {
				K.model_checking = cmd.getOptionValue("ltlmc");
			}

			// printing the output according to the given options
			if (K.help) {
				printUsage(cmd_options.getOptions());
				System.exit(0);
			}
			if (K.version) {
				printVersion();
				System.exit(0);
			}

			String[] remainingArguments = null;
			if (cmd_options.getCommandLine().getOptions().length > 0) {
				remainingArguments = cmd.getArgs();
			} else {
				remainingArguments = cmds;
			}
			String programArg = new String();
			if (remainingArguments.length > 0) {
				programArg = new File(remainingArguments[0]).getCanonicalPath();
				K.pgm = programArg;
			}
			if (K.pgm == null) {
				Error.usageError("missing required <file> argument");
			}
			File pgmFile = new File(K.pgm);
			if (!pgmFile.exists()) {
				Error.report("\nProgram file does not exist: " + K.pgm);
			}
			String lang = FileUtil.getExtension(K.pgm, ".", K.fileSeparator);

			// by default
			if (!cmd.hasOption("k-definition")) {
				K.k_definition = new File(K.userdir).getCanonicalPath() + K.fileSeparator + lang;
			}

			initOptions(K.userdir, lang);

			if (!cmd.hasOption("compiled-def")) {
				resolveOption("compiled-def", lang, cmd);
			}
			if (!cmd.hasOption("main-module")) {
				resolveOption("main-module", lang, cmd);
			}
			if (!cmd.hasOption("syntax-module")) {
				resolveOption("syntax-module", lang, cmd);
			}
 
			if (! K.k_definition.endsWith(".k")) {
				K.k_definition = K.k_definition + ".k";
			}

			if (K.compiled_def == null) {
				Error.report("\nCould not find a compiled K definition.");
			}
			File compiledFile = new File(K.compiled_def);
			if (!compiledFile.exists()) {
				Error.report("\nCould not find compiled definition: " + K.compiled_def + "\nPlease compile the definition by using `kompile'.");
			}

			/*
			 * System.out.println("K.k_definition=" + K.k_definition);
			 * System.out.println("K.syntax_module=" + K.syntax_module);
			 * System.out.println("K.main_module=" + K.main_module);
			 */

			// in KAST variable we obtain the output from running kast process on a program defined in K
			String KAST = new String();
			RunProcess rp = new RunProcess();

			String k3jar = new File(K.kast).getParent() + K.fileSeparator + "java" + K.fileSeparator + "k3.jar";
			KAST = rp.runParser(k3jar, K.parser, K.k_definition, K.pgm, true);

			String s = new String();
			if (K.do_search) {
				if ("search".equals(K.maude_cmd)) {
					s = "set show command off ." + K.lineSeparator + "search #eval(__((_|->_((# \"$PGM\"(.List{K})) ,(" + KAST + "))),(.).Map)) =>! B:Bag .";
				} else {
					Error.report("For the do-search option you need to specify that --maude-cmd=search");
				}
			} else if (cmd.hasOption("maude-cmd")) {
				s = "set show command off ." + K.lineSeparator + K.maude_cmd + " #eval(__((_|->_((# \"$PGM\"(.List{K})) ,(" + KAST + "))),(.).Map)) .";
			} else if (cmd.hasOption("xsearch-pattern")) {
				s = "set show command off ." + K.lineSeparator + "search #eval(__((_|->_((# \"$PGM\"(.List{K})) ,(" + KAST + "))),(.).Map)) " + K.xsearch_pattern + " .";
				//s = "set show command off ." + K.lineSeparator + "search #eval(__((_|->_((# \"$PGM\"(.List{K})) ,(" + KAST + "))),(.).Map)) " + "\"" + K.xsearch_pattern + "\"" + " .";
			} else {
				s = "set show command off ." + K.lineSeparator + "erew #eval(__((_|->_((# \"$PGM\"(.List{K})) ,(" + KAST + "))),(.).Map)) .";
			}

			if (K.trace) {
				s = "set trace on ." + K.lineSeparator + s;
			}
			
			StringBuilder sb = new StringBuilder();
			if (K.model_checking.length() > 0) {
				//run kast for the formula to be verified
				File formulaFile = new File(K.model_checking);
				String KAST1 = new String();
				if (!formulaFile.exists()) {
					//Error.silentReport("\nThe specified argument does not exist as a file on the disc; it may represent a direct formula: " + K.model_checking);
					//assume that the specified argument is not a file and maybe represents a formula
					KAST1 = rp.runParser(k3jar, K.parser, K.k_definition, K.model_checking, false);
				}
				else {
					//the specified argument represents a file
					KAST1 = rp.runParser(k3jar, K.parser, K.k_definition, K.model_checking, true);
				}
				
				sb.append("load " + K.compiled_def);
				sb.append(K.lineSeparator + K.lineSeparator);
				sb.append("mod MCK is");
				sb.append(" including " + K.main_module + " .");
				sb.append(K.lineSeparator + K.lineSeparator);
				sb.append(" op #initConfig : -> Bag .");
				sb.append(K.lineSeparator + K.lineSeparator);
				sb.append(" eq #initConfig =");
				sb.append(K.lineSeparator);
				sb.append("  #eval(__((_|->_((# \"$PGM\"(.List{K})) ,(" + KAST + "))),(.).Map)) .");
				sb.append(K.lineSeparator);
				sb.append("endm");
				sb.append(K.lineSeparator + K.lineSeparator);
				sb.append("red");
				sb.append(K.lineSeparator);
				sb.append("_`(_`)(('modelCheck`(_`,_`)).KLabel,_`,`,_(_`(_`)(#_(KItem`(_`)(#initConfig)),.List`{K`}),");
				sb.append(K.lineSeparator);
				sb.append(KAST1);
				sb.append(")");
				sb.append(K.lineSeparator);
				sb.append(") .");
				s = sb.toString();
			}

			FileUtil.createFile(K.maude_in, s);

			// run IOServer
			File outFile = FileUtil.createFile(K.maude_out);
			File errFile = FileUtil.createFile(K.maude_err);
				
			if (K.log_io) {
				KRunner.main(new String[] { "--maudeFile", K.compiled_def, "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath(), "--createLogs" });
			}
			if (!K.io) {
				KRunner.main(new String[] { "--maudeFile", K.compiled_def, "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath(), "--noServer" });
			} else {
				KRunner.main(new String[] { "--maudeFile", K.compiled_def, "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath() });
			}
			
			// check whether Maude produced errors
			if (errFile.exists()) {
				String content = FileUtil.getFileContent(K.maude_err);
				if (content.length() > 0) {
					Error.externalReport("Fatal: Maude produced warnings or errors:\n" + content);
				}
			}
			
			if ("search".equals(K.maude_cmd) && K.do_search) {
				printSearchResults();
			}
			if ("pretty".equals(K.output_mode)) {
				PrettyPrintOutput p = new PrettyPrintOutput(cmd);
			    p.preprocessDoc(K.maude_output, K.processed_maude_output);
				String red = p.processDoc(K.processed_maude_output);
				AnsiConsole.out.println(red);
			} else if ("raw".equals(K.output_mode)) {
				String output = new String();
				if (K.model_checking.length() > 0) {
					output = FileUtil.parseModelCheckingOutputMaude(K.maude_out);
				} 
				else {
					if ("search".equals(K.maude_cmd)) {
						List<String> l = FileUtil.parseSearchOutputMaude(K.maude_out);
						if (l.size() > 0) {
							output = l.get(0);
						}
						else {
							output = "";
						}
					} else if ("erewrite".equals(K.maude_cmd)) {
						output = FileUtil.parseResultOutputMaude(K.maude_out);
					}
				}
				System.out.println(output);

			} else if ("none".equals(K.output_mode)) {
				System.out.print("");
			} else {
				Error.report(K.output_mode + " is not a valid value for output-mode option");
			}

			if (K.statistics) {
				printStatistics(cmd);
			}

			// save the pretty-printed output of jkrun in a file
			//FileUtil.createFile(K.krun_output, prettyOutput);
			
			ProcessBean bean = new ProcessBean();
			bean.setExitCode(0);
			System.exit(bean.getExitCode());

		} catch (ParseException exp) {
			System.out.println("Unexpected exception:" + exp.getMessage());
			ProcessBean bean = new ProcessBean();
			bean.setExitCode(1);
			System.exit(bean.getExitCode());
		} catch (IOException e) {
			System.out.println(e.getMessage());
			ProcessBean bean = new ProcessBean();
			bean.setExitCode(1);
			System.exit(bean.getExitCode());
		} catch (Exception e) {
			System.out.println("You provided bad program arguments!");
			e.printStackTrace();
			ProcessBean bean = new ProcessBean();
			bean.setExitCode(1);
			printUsage(cmd_options.getOptions());
			System.exit(bean.getExitCode());
		}
	}

	public static void main(String[] args) {
		execute_Krun(args);

	}

}
