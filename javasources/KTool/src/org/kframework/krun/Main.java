package org.kframework.krun;

import com.thoughtworks.xstream.XStream;
import jline.*;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.fusesource.jansi.AnsiConsole;
import org.kframework.backend.maude.MaudeFilter;
import org.kframework.compile.ConfigurationCleaner;
import org.kframework.compile.FlattenModules;
import org.kframework.compile.transformers.AddTopCellConfig;
import org.kframework.compile.transformers.FlattenSyntax;
import org.kframework.compile.utils.MetaK;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.api.*;
import org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor;
import org.kframework.utils.DefinitionLoader;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import edu.uci.ics.jung.graph.*;

import java.io.*;
import java.util.*;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class Main {

	private static final String USAGE_KRUN = "krun [options] <file>" + K.lineSeparator;
	private static final String USAGE_DEBUG = "Enter one of the following commands without \"--\" in front. " + K.lineSeparator + "For autocompletion press TAB key and for accessing the command"
			+ K.lineSeparator + "history use up and down arrows." + K.lineSeparator;
	private static final String HEADER = "";
	private static final String FOOTER = "";

	// needed for displaying the krun help
	public static void printKRunUsage(Options options) {
		HelpFormatter helpFormatter = new HelpFormatter();
		helpFormatter.setOptionComparator(new CommandlineOptions.OptionComparator());
		helpFormatter.setWidth(79);
		helpFormatter.printHelp(USAGE_KRUN, HEADER, options, FOOTER);
		System.out.println();
	}

	// needed for displaying the krun debugger help
	public static void printDebugUsage(Options options) {
		HelpFormatter helpFormatter = new HelpFormatter();
		helpFormatter.setOptionComparator(new CommandlineOptions.OptionComparator());
		helpFormatter.setWidth(79);
		helpFormatter.printHelp(USAGE_DEBUG, HEADER, options, FOOTER);
		System.out.println();
	}

	public static void printVersion() {
		System.out.println("JKrun 0.2.0\n" + "Copyright (C) 2012 Necula Emilian & Raluca");
	}

	// find the maude compiled definitions on the disk
	public static String initOptions(String path) {
		String result = null;
		//String path_ = null;
		String fileName = null;
		StringBuilder str = new StringBuilder();
		int count = 0;

		try {
			File[] maudeFiles = FileUtil.searchSubFolders(path, ".*-kompiled");
			for (File maudeFile : maudeFiles) {
				String fullPath = maudeFile.getCanonicalPath();
				if (fullPath.endsWith("-kompiled")) {
					result = fullPath;
					str.append("\"./" + maudeFile.getName() + "\" ");
					count++;
				}
			}
			if (count > 1) {
				Error.report("Multiple compiled definitions found. Please specify one of: " + str.toString() + "with --compiled-def");
			} else if (count == 1) {
				return result;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		return result;
	}

	// set the main-module, syntax-module and k-definition according to their correlation with compiled-def
	public static void resolveOption(String optionName, CommandLine cmd) {
		String s, str;
		if (K.k_definition != null) {
			s = FileUtil.dropKExtension(K.k_definition, ".", K.fileSeparator);
			int sep = s.lastIndexOf(K.fileSeparator);
			str = s.substring(sep + 1).toUpperCase();
		} else {
			// using --compiled-def
			if (K.compiled_def != null && K.compiled_def.endsWith("-kompiled")) {
				s = K.compiled_def.substring(0, K.compiled_def.lastIndexOf("-kompiled"));
				int sep = s.lastIndexOf(K.fileSeparator);
				str = s.substring(sep + 1).toUpperCase();
			} else {
				s = null;
				str = null;
			}
		}

		int index;

		if (optionName == "compiled-def") {
			if (cmd.hasOption("k-definition")) {
				K.compiled_def = s + "-kompiled";
			} else {
				K.compiled_def = initOptions(K.userdir);
				if (K.compiled_def != null) {
					index = K.compiled_def.indexOf("-kompiled");
					K.k_definition = K.compiled_def.substring(0, index);
				}
			}
		} else if (optionName == "main-module") {
			K.main_module = K.definition.getMainModule();
		} else if (optionName == "syntax-module") {
			K.syntax_module = K.definition.getMainSyntaxModule();
		}
	}

	private static String parseTerm(String value) throws Exception {

		ASTNode term = org.kframework.utils.DefinitionLoader.parseCmdString(value, "", "Command line argument");
		term = term.accept(new FlattenSyntax());
		MaudeFilter maudeFilter = new MaudeFilter();
		term.accept(maudeFilter);
		return maudeFilter.getResult();
	}

	public static Term plug(Map<String, String> args) throws TransformerException {
		Configuration cfg = MetaK.getConfiguration(K.kompiled_def);
		ASTNode cfgCleanedNode = null;
		try {
			cfgCleanedNode = new ConfigurationCleaner().transform(cfg);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Term cfgCleaned;
		if (cfgCleanedNode == null) {
			cfgCleaned = new Empty(MetaK.Constants.Bag);
		} else {
			if (!(cfgCleanedNode instanceof Configuration)) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
						KExceptionGroup.INTERNAL,
						"Configuration Cleaner failed.",
						cfg.getFilename(), cfg.getLocation()));
			}
			cfgCleaned = ((Configuration)cfgCleanedNode).getBody();
		}

		Map<String, Term> termArgs = new HashMap<String, Term>();
		for (String key : args.keySet()) {
			termArgs.put(key, new BackendTerm("", args.get(key))); // the SubstitutionFilter automatically inserts the sort of BackendTerms
		}
		
		return (Term) cfgCleaned.accept(new SubstitutionFilter(termArgs));
	}

	public static Term makeConfiguration(String kast, String stdin, RunProcess rp, boolean hasTerm) throws TransformerException {
		
		if(hasTerm) {
			if(kast == null) {
				kast = rp.runParser(K.parser, K.term, false, null);
				return new BackendTerm("Bag", kast);
			} else {
				Error.report("You cannot specify both the term and the configuration variables.");
			}
		}
		
		HashMap<String, String> output = new HashMap<String, String>();
		boolean hasPGM = false;
		Enumeration<Object> en = K.configuration_variables.keys();
		while (en.hasMoreElements()) {
			String name = (String) en.nextElement();
			String value = K.configuration_variables.getProperty(name);
			String parser = K.cfg_parsers.getProperty(name);
			// TODO: get sort from configuration term in definition and pass it here
			String parsed = "";
			if (parser == null) {
				try {
					parsed = parseTerm(value);
				} catch (Exception e1) {
					e1.printStackTrace();
					Error.report(e1.getMessage());
				}
			} else {
				parsed = rp.runParser(parser, value, false, null);
			}
			output.put("$" + name, parsed);
			hasPGM = hasPGM || name.equals("$PGM");
		}
		if (!hasPGM && kast != null) {
			output.put("$PGM", kast);
		}
		if (!K.io && stdin == null) {
			stdin = "";
		}
		if (stdin != null) {
			output.put("$noIO", "#noIO");
			output.put("$stdin", "# \"" + stdin + "\\n\"(.KList)");
		} else {
			output.put("$noIO", "(.).List");
			output.put("$stdin", "(.).K");
		}
		return plug(output);
	}

	// execute krun in normal mode (i.e. not in debug mode)
	public static void normalExecution(String KAST, String lang, RunProcess rp, CommandlineOptions cmd_options) {
		try {
			List<String> red = new ArrayList<String>();
			StringBuilder aux1 = new StringBuilder();
			CommandLine cmd = cmd_options.getCommandLine();

			KRun krun = new MaudeKRun();
			KRunResult<?> result = null;
			try {
				if (K.do_search) {
					if ("search".equals(K.maude_cmd)) {
						BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
						String buffer = "";
						// detect if the input comes from console or redirected from a pipeline
						Console c = System.console();
						if (c == null && br.ready()) {
							try {
								buffer = br.readLine();
							} catch (IOException ioe) {
								ioe.printStackTrace();
							} finally {
								if (br != null) {
									try {
										br.close();
									} catch (IOException e) {
										e.printStackTrace();
									}
								}
							}
						}
						Integer depth = null;
						Integer bound = null;
						if (cmd.hasOption("bound") && cmd.hasOption("depth")) {
							bound = Integer.parseInt(K.bound);
							depth = Integer.parseInt(K.depth);
						} else if (cmd.hasOption("bound")) {
							bound = Integer.parseInt(K.bound);
						} else if (cmd.hasOption("depth")) {
							depth = Integer.parseInt(K.depth);
						}
						ASTNode pattern = DefinitionLoader.parsePattern(K.pattern, "Command line pattern");
						CollectVariablesVisitor vars = new CollectVariablesVisitor();
						pattern.accept(vars);
						Set<String> varNames = vars.getVars().keySet();

						pattern = new RuleCompilerSteps(K.definition).compile((Rule) pattern, null);

						Rule patternRule = (Rule) pattern;
						result = krun.search(bound, depth, K.searchType, patternRule, makeConfiguration(KAST, buffer, rp, (K.term != null)), varNames);
					} else {
						Error.report("For the search option you need to specify that --maude-cmd=search");
					}
				} else if (K.model_checking.length() > 0) {
					// run kast for the formula to be verified
					File formulaFile = new File(K.model_checking);
					String KAST1 = new String();
					if (!formulaFile.exists()) {
						// Error.silentReport("\nThe specified argument does not exist as a file on the disc; it may represent a direct formula: " + K.model_checking);
						// assume that the specified argument is not a file and maybe represents a formula
						KAST1 = rp.runParser(K.parser, K.model_checking, true, "LTLFormula");
					} else {
						// the specified argument represents a file
						KAST1 = rp.runParser(K.parser, K.model_checking, false, "LTLFormula");
					}

					result = krun.modelCheck(new BackendTerm("K", KAST1), makeConfiguration(KAST, null, rp, (K.term != null)));
				} else {
					result = krun.run(makeConfiguration(KAST, null, rp, (K.term != null)));
				}
			} catch (KRunExecutionException e) {
				rp.printError(e.getMessage(), lang);
				System.exit(1);
			}

			if ("pretty".equals(K.output_mode)) {
				String output = result.toString();
				aux1.append(output);
				if (!cmd.hasOption("output")) {
					AnsiConsole.out.println(output);
				}
				// print search graph
				if ("search".equals(K.maude_cmd) && K.do_search && K.showSearchGraph) {
					System.out.println(K.lineSeparator + "The search graph is:" + K.lineSeparator);
					@SuppressWarnings("unchecked")
					KRunResult<SearchResults> searchResult = (KRunResult<SearchResults>)result;
					AnsiConsole.out.println(searchResult.getResult().getGraph());
					// offer the user the possibility to turn execution into debug mode
					while (true) {
						System.out.print(K.lineSeparator + "Do you want to enter in debug mode? (y/n):");
						BufferedReader stdin = new BufferedReader(new InputStreamReader(System.in));
						String input = stdin.readLine();
						if (input == null) {
							K.debug = false;
							System.out.println();
							break;
						}
						if (input.equals("y")) {
							K.debug = true;
							debugExecution(KAST, lang, searchResult);
						} else if (input.equals("n")) {
							K.debug = false;
							break;
						} else {
							System.out.println("You should specify one of the possible answers:y or n");
						}
					}
				}
			} else if ("raw".equals(K.output_mode)) {
				String output = result.getRawOutput();
				;
				if (!cmd.hasOption("output")) {
					System.out.println(output);
				}
				aux1.append(output);

			} else if ("none".equals(K.output_mode)) {
				System.out.print("");
			} else {
				Error.report(K.output_mode + " is not a valid value for output-mode option");
			}

			// save the pretty-printed output of jkrun in a file
			if (cmd.hasOption("output")) {
				FileUtil.createFile(K.output, aux1.toString());
			}

			System.exit(0);
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(1);
		} catch (Exception e) {
			System.out.println("You provided bad program arguments!");
			e.printStackTrace();
			printKRunUsage(cmd_options.getOptions());
			System.exit(1);
		}

	}

	// execute krun in debug mode (i.e. step by step execution)
	// isSwitch variable is true if we enter in debug execution from normal execution (we use the search command with --graph option)
	public static void debugExecution(String kast, String lang, KRunResult<SearchResults> state) {
		try {
			// adding autocompletion and history feature to the stepper internal commandline by using the JLine library
			ConsoleReader reader = new ConsoleReader();
			reader.setBellEnabled(false);

			List<Completor> argCompletor = new LinkedList<Completor>();
			argCompletor.add(new SimpleCompletor(new String[] { "help", "abort", "resume", "step", "step-all", "select", "show-search-graph", "show-node", "show-edge" }));
			argCompletor.add(new FileNameCompletor());
			List<Completor> completors = new LinkedList<Completor>();
			completors.add(new ArgumentCompletor(argCompletor));
			reader.addCompletor(new MultiCompletor(completors));

			String compiledFile = new File(K.compiled_def + K.fileSeparator + "main.maude").getCanonicalPath();
			String maudeCmd = new String();
			File outFile = FileUtil.createFile(K.maude_out);
			File errFile = FileUtil.createFile(K.maude_err);
			RunProcess rp = new RunProcess();
			List<String> red = null;
			KRun krun = new MaudeKRun();
			KRunDebugger debugger;
			if (state == null) {
				Term t = makeConfiguration(kast, null, rp, (K.term != null));
				debugger = krun.debug(t);
				System.out.println("After running one step of execution the result is:");
				AnsiConsole.out.println(debugger.printState(debugger.getCurrentState()));
			} else {
				debugger = krun.debug(state.getResult());
			}

			while (true) {
				System.out.println();
				String input = reader.readLine("Command > ");
				if (input == null) {
					//probably pressed ^D
					System.out.println();
					System.exit(0);
				}

				// construct the right command line input when we specify the "step" option with an argument (i.e. step=3)
				input = input.trim();
				String[] tokens = input.split(" ");
				// store the tokens that are not a blank space
				List<String> items = new ArrayList<String>();
				for (int i = 0; i < tokens.length; i++) {
					if ((!(tokens[i].equals(" ")) && (!tokens[i].equals("")))) {
						items.add(tokens[i]);
					}
				}
				StringBuilder aux = new StringBuilder();
				// excepting the case of a command like: help
				if (items.size() > 1) {
					for (int i = 0; i < items.size(); i++) {
						if (i > 0) {
							aux.append("=");
							aux.append(items.get(i));
						} else if (i == 0) {
							aux.append(items.get(i));
						}
					}
					input = aux.toString();
				}
				// apply trim to remove possible blank spaces from the inserted command
				String[] cmds = new String[] { "--" + input };
				CommandlineOptions cmd_options = new CommandlineOptions();
				CommandLine cmd = cmd_options.parse(cmds);
				// when an error occurred during parsing the commandline continue the execution of the stepper
				if (cmd == null) {
					continue;
				} else {
					if (cmd.hasOption("help")) {
						printDebugUsage(cmd_options.getOptions());
					}
					if (cmd.hasOption("abort")) {
						System.exit(0);
					}
					if (cmd.hasOption("resume")) {
						try {
							debugger.resume();
							AnsiConsole.out.println(debugger.printState(debugger.getCurrentState()));
						} catch (IllegalStateException e) {
							Error.silentReport("Wrong command: If you previously used the step-all command you must select" + K.lineSeparator
									+ "first a solution with step command before executing steps of rewrites!");
						}
					}
					// one step execution (by default) or more if you specify an argument
					if (cmd.hasOption("step")) {
						// by default execute only one step at a time
						String arg = new String("1");
						String[] remainingArguments = null;
						remainingArguments = cmd.getArgs();
						if (remainingArguments.length > 0) {
							arg = remainingArguments[0];
						}
						try {
							int steps = Integer.parseInt(arg);
							debugger.step(steps);
							AnsiConsole.out.println(debugger.printState(debugger.getCurrentState()));
						} catch (NumberFormatException e) {
							Error.silentReport("Argument to step must be an integer.");
						} catch (IllegalStateException e) {
							Error.silentReport("Wrong command: If you previously used the step-all command you must select" + K.lineSeparator
									+ "first a solution with step command before executing steps of rewrites!");
						}
					}
					if (cmd.hasOption("step-all")) {
						// by default compute all successors in one transition
						String arg = new String("1");
						String[] remainingArguments = null;
						remainingArguments = cmd.getArgs();
						if (remainingArguments.length > 0) {
							arg = remainingArguments[0];
						}
						try {
							int steps = Integer.parseInt(arg);	
							SearchResults states = debugger.stepAll(steps);
							AnsiConsole.out.println(states);
								
						} catch (NumberFormatException e) {
							Error.silentReport("Argument to step-all must be an integer.");
						} catch (IllegalStateException e) {
							Error.silentReport("Wrong command: If you previously used the step-all command you must select" + K.lineSeparator
									+ "first a solution with step command before executing steps of rewrites!");
						}
					}
					// "select n7" or "select 3" are both valid commands
					if (cmd.hasOption("select")) {
						String arg = new String();
						arg = cmd.getOptionValue("select").trim();
						try {
							int stateNum = Integer.parseInt(arg);
							debugger.setCurrentState(stateNum);
							AnsiConsole.out.println(debugger.printState(debugger.getCurrentState()));
						} catch (NumberFormatException e) {
							Error.silentReport("Argument to select must bean integer.");
						} catch (IllegalArgumentException e) {
							System.out.println("A node with the specified state number could not be found in the" + K.lineSeparator + "search graph");
						}
					}
					if (cmd.hasOption("show-search-graph")) {
						System.out.println(K.lineSeparator + "The search graph is:" + K.lineSeparator);
						System.out.println(debugger.getGraph());
					}
					if (cmd.hasOption("show-node")) {
						String nodeId = cmd.getOptionValue("show-node").trim();
						try {
							int stateNum = Integer.parseInt(nodeId);
							AnsiConsole.out.println(debugger.printState(stateNum));
						} catch (NumberFormatException e) {
							Error.silentReport("Argument to select node to show must be an integer.");
						} catch (IllegalArgumentException e) {
							System.out.println("A node with the specified state number could not be found in the" + K.lineSeparator + "search graph");
						}
					}
					if (cmd.hasOption("show-edge")) {
						String[] vals = cmd.getOptionValues("show-edge");
						vals = vals[0].split("=",2);
						try {
							int state1 = Integer.parseInt(vals[0].trim());
							int state2 = Integer.parseInt(vals[1].trim());
							AnsiConsole.out.println(debugger.printEdge(state1, state2));
						} catch (ArrayIndexOutOfBoundsException e) {
							Error.silentReport("Must specify two nodes with an edge between them.");
						} catch (NumberFormatException e) {
							Error.silentReport("Arguments to select edge to show must be integers.");
						} catch (IllegalArgumentException e) {
							System.out.println("An edge with the specified endpoints could not be found in the" + K.lineSeparator + "search graph");
						}
					}
				}
			}
		} catch (Exception e) {
			e.printStackTrace();
			System.exit(1);
		}

	}

	/**
	 * @param cmds
	 *            represents the arguments/options given to jkrun command..
	 */
	public static void execute_Krun(String cmds[]) {
		// delete temporary krun directory
		FileUtil.deleteDirectory(new File(K.krunDir));
		Runtime.getRuntime().addShutdownHook(new Thread() {
			public void run() {
				try {
					FileUtil.renameFolder(K.krunTempDir, K.krunDir);
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		});

		CommandlineOptions cmd_options = new CommandlineOptions();
		CommandLine cmd = cmd_options.parse(cmds);
		try {

			// Parse the program arguments

			if (cmd.hasOption("search") || cmd.hasOption("do-search") || cmd.hasOption("search-final") || cmd.hasOption("search-all") || cmd.hasOption("search-one-step")
					|| cmd.hasOption("search-one-or-more-steps")) {
				K.maude_cmd = "search";
				K.io = false;
				K.do_search = true;
				if (cmd.hasOption("search") && cmd.hasOption("depth")) {
					K.searchType = SearchType.STAR;
				}
			}
			if (cmd.hasOption("search-final")) {
				K.searchType = SearchType.FINAL;
			}
			if (cmd.hasOption("search-all")) {
				K.searchType = SearchType.STAR;
			}
			if (cmd.hasOption("search-one-step")) {
				K.searchType = SearchType.ONE;
			}
			if (cmd.hasOption("search-one-or-more-steps")) {
				K.searchType = SearchType.PLUS;
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
			if (cmd.hasOption("term")) {
				K.term = cmd.getOptionValue("term");
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
			// k-definition beats compiled-def in a fight
			if (cmd.hasOption("compiled-def") && !cmd.hasOption("k-definition")) {
				K.compiled_def = new File(cmd.getOptionValue("compiled-def")).getCanonicalPath();
			}
			if (cmd.hasOption("maude-cmd")) {
				K.maude_cmd = cmd.getOptionValue("maude-cmd");
			}
			/*
			 * if (cmd.hasOption("xsearch-pattern")) { K.maude_cmd = "search"; K.do_search = true; K.xsearch_pattern = cmd.getOptionValue("xsearch-pattern"); // System.out.println("xsearch-pattern:" +
			 * K.xsearch_pattern); }
			 */
			if (cmd.hasOption("pattern")) {
				K.pattern = cmd.getOptionValue("pattern");
			}
			if (cmd.hasOption("bound")) {
				K.bound = cmd.getOptionValue("bound");
			}
			if (cmd.hasOption("depth")) {
				K.depth = cmd.getOptionValue("depth");
			}
			if (cmd.hasOption("graph")) {
				K.showSearchGraph = true;
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
			if (cmd.hasOption("profile")) {
				K.profile = true;
			}
			if (cmd.hasOption("pgm")) {
				K.pgm = cmd.getOptionValue("pgm");
			}
			if (cmd.hasOption("ltlmc")) {
				K.model_checking = cmd.getOptionValue("ltlmc");
			}
			if (cmd.hasOption("deleteTempDir")) {
				K.deleteTempDir = true;
			}
			if (cmd.hasOption("no-deleteTempDir")) {
				K.deleteTempDir = false;
			}
			if (cmd.hasOption("output")) {
				if (!cmd.hasOption("color")) {
					K.color = false;
				}
				K.output = new File(cmd.getOptionValue("output")).getCanonicalPath();
			}
			if (cmd.hasOption("c")) {
				
				if(K.term != null)
				{
					Error.report("You cannot specify both the term and the configuration variables.");
				}
				
				K.configuration_variables = cmd.getOptionProperties("c");
				String parser = null;
				for (Option opt : cmd.getOptions()) {
					if (opt.equals(cmd_options.getOptions().getOption("c")) && parser != null) {
						K.cfg_parsers.setProperty(opt.getValue(0), parser);
					}
					if (opt.equals(cmd_options.getOptions().getOption("cfg-parser"))) {
						parser = opt.getValue();
					}
				}
			}

			// printing the output according to the given options
			if (K.help) {
				printKRunUsage(cmd_options.getOptions());
				System.exit(0);
			}
			if (K.version) {
				printVersion();
				System.exit(0);
			}
			if (K.deleteTempDir) {
				File[] folders = FileUtil.searchSubFolders(K.kdir, "krun\\d+");
				if (folders != null && folders.length > 0) {
					for (int i = 0; i < folders.length; i++) {
						FileUtil.deleteDirectory(folders[i]);
					}
				}
			}

			String[] remainingArguments = null;
			if (cmd_options.getCommandLine().getOptions().length > 0) {
				remainingArguments = cmd.getArgs();
			} else {
				remainingArguments = cmds;
			}
			String programArg = new String();
			if (remainingArguments.length > 0) {
				programArg = remainingArguments[0];
				K.pgm = programArg;
			}
			String lang = null;
			if (K.pgm != null) {
				File pgmFile = new File(K.pgm);
				if (pgmFile.exists()) {
					lang = FileUtil.getExtension(K.pgm, ".", K.fileSeparator);
				}
			}

			// by default
			if (!cmd.hasOption("k-definition") && !cmd.hasOption("compiled-def") && lang != null) {
				K.k_definition = new File(K.userdir).getCanonicalPath() + K.fileSeparator + lang;
			}

			if (K.compiled_def == null) {
				resolveOption("compiled-def", cmd);
			}

			if (K.k_definition != null && !K.k_definition.endsWith(".k")) {
				K.k_definition = K.k_definition + ".k";
			}

			if (K.compiled_def == null) {
				Error.report("Could not find a compiled K definition. Please ensure that either a compiled K definition exists in the current directory with its default name, or that --k-definition or --compiled-def have been specified.");
			}
			File compiledFile = new File(K.compiled_def);
			if (!compiledFile.exists()) {
				Error.report("\nCould not find compiled definition: " + K.compiled_def + "\nPlease compile the definition by using `kompile'.");
			}

			DefinitionHelper.dotk = new File(new File(K.compiled_def).getParent() + File.separator + ".k");
			if (!DefinitionHelper.dotk.exists()) {
				DefinitionHelper.dotk.mkdirs();
			}
			DefinitionHelper.kompiled = new File(K.compiled_def);
			K.kdir = DefinitionHelper.dotk.getCanonicalPath();
			K.setKDir();
			/*
			 * System.out.println("K.k_definition=" + K.k_definition); System.out.println("K.syntax_module=" + K.syntax_module); System.out.println("K.main_module=" + K.main_module);
			 * System.out.println("K.compiled_def=" + K.compiled_def);
			 */

			// in KAST variable we obtain the output from running kast process on a program defined in K
			String KAST = new String();
			RunProcess rp = new RunProcess();

			if (!DefinitionHelper.initialized) {
				XStream xstream = new XStream();
				xstream.aliasPackage("k", "ro.uaic.info.fmse.k");

				org.kframework.kil.Definition javaDef = (org.kframework.kil.Definition) xstream.fromXML(new File(K.compiled_def + "/defx.xml"));
				// This is essential for generating maude
				javaDef = new FlattenModules().compile(javaDef, null);
				javaDef = (org.kframework.kil.Definition) javaDef.accept(new AddTopCellConfig());
				javaDef.preprocess();
				K.definition = javaDef;

				org.kframework.parser.concrete.KParser.ImportTbl(K.compiled_def + "/def/Concrete.tbl");
				org.kframework.parser.concrete.KParser.ImportTblGround(K.compiled_def + "/ground/Concrete.tbl");

				org.kframework.kil.Definition javaDefKompiled = (org.kframework.kil.Definition) xstream.fromXML(new File(K.compiled_def + "/defx-kompiled.xml"));
				K.kompiled_def = javaDefKompiled;
			}

			if (!cmd.hasOption("main-module")) {
				resolveOption("main-module", cmd);
			}
			if (!cmd.hasOption("syntax-module")) {
				resolveOption("syntax-module", cmd);
			}

			if (K.pgm != null) {
				KAST = rp.runParser(K.parser, K.pgm, false, null);
			} else {
				KAST = null;
			}
			
			if(K.term != null) {
				if(K.parser.equals("kast")) {
					GlobalSettings.whatParser = GlobalSettings.ParserType.GROUND;
				}
			}
	
			GlobalSettings.kem.print();

			if (!K.debug) {
				normalExecution(KAST, lang, rp, cmd_options);
			} else {
				if (K.do_search) {
					Error.report("Cannot specify --search with --debug. In order to search inside the debugger, use the step-all command.");
				}
				debugExecution(KAST, lang, null);
			}
		} catch (IOException e) {
			e.printStackTrace();
			System.exit(1);
		} catch (Exception e) {
			System.out.println("You provided bad program arguments!");
			e.printStackTrace();
			printKRunUsage(cmd_options.getOptions());
			System.exit(1);
		}
	}

	public static void main(String[] args) {

		execute_Krun(args);

	}

}
