package org.kframework.krun;

import org.kframework.krun.runner.KRunner;

import java.io.File;
import java.util.List;
import java.util.Map;

public class KRun {

	private PrettyPrintOutput p;

	private KRun(String maudeCmd, boolean ioServer) throws Exception {
		FileUtil.createFile(K.maude_in, maudeCmd);
		File outFile = FileUtil.createFile(K.maude_out);
		File errFile = FileUtil.createFile(K.maude_err);

		if (K.log_io) {
			KRunner.main(new String[] { "--maudeFile", K.compiled_def, "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath(), "--createLogs" });
		}
		if (!ioServer) {
			KRunner.main(new String[] { "--maudeFile", K.compiled_def, "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath(), "--noServer" });
		} else {
			KRunner.main(new String[] { "--maudeFile", K.compiled_def, "--moduleName", K.main_module, "--commandFile", K.maude_in, "--outputFile", outFile.getCanonicalPath(), "--errorFile", errFile.getCanonicalPath() });
		}

		if (errFile.exists()) {
			String content = FileUtil.getFileContent(K.maude_err);
			if (content.length() > 0) {
				throw new KRunExecutionException(content);
			}
		}

		p = new PrettyPrintOutput(K.color);
		p.preprocessDoc(K.maude_output, K.processed_maude_output);
	}


	public static KRun run(String maudeCmd, Map<String, String> cfg) throws Exception {
		String cmd = "set show command off ." + K.lineSeparator + maudeCmd + " #eval(" + flatten(cfg) + ") .";
		if(K.trace) {
			cmd = "set trace on ." + K.lineSeparator + cmd;
		}

		return new KRun(cmd, !cfg.containsKey("noIO"));
	}

	public static KRun search(String bound, String depth, String pattern, Map<String, String> cfg, boolean showSearchGraph) throws Exception {
		String cmd = "set show command off ." + K.lineSeparator + "search ";
		if (bound != null && depth != null) {
			cmd += "[" + bound + "," + depth + "] ";
		} else if (bound != null) {
			cmd += "[" + bound + "] ";
		} else if (depth != null) {
			cmd += "[," + depth + "] ";
		}
		cmd += "#eval(" + flatten(cfg) + ") " + pattern + " .";
		if (showSearchGraph) {
			cmd += K.lineSeparator + "show search graph .";
		}
		if (K.trace) {
			cmd = "set trace on ." + K.lineSeparator + cmd;
		}
		return new KRun(cmd, !cfg.containsKey("noIO"));
	}

	public static KRun modelCheck(String formula, Map<String, String> cfg) throws Exception {
		String cmd = "mod MCK is" + K.lineSeparator + " including " + K.main_module + " ." + K.lineSeparator + K.lineSeparator + " op #initConfig : -> Bag ." + K.lineSeparator + K.lineSeparator + " eq #initConfig  =" + K.lineSeparator + "  #eval(" + flatten(cfg) + ") ." + K.lineSeparator + "endm" + K.lineSeparator + K.lineSeparator + "red" + K.lineSeparator + "_`(_`)(('modelCheck`(_`,_`)).KLabel,_`,`,_(_`(_`)(Bag2KLabel(#initConfig),.List`{K`})," + K.lineSeparator + formula + ")" + K.lineSeparator + ") .";
		return new KRun(cmd, false);
	}

	public List<String> prettyPrint() {
		return p.processDoc(K.processed_maude_output);
	}

	public String printSearchGraph() {
		return p.printSearchGraph(K.processed_maude_output);
	}

	public String printNodeSearchGraph(String nodeName) {
		return p.printNodeSearchGraph(K.processed_maude_output, nodeName);
	}

	public String rawOutput() {
		return FileUtil.getFileContent(K.maude_out);
	}

	public static String flatten(Map<String, String> cfg) {
		int items = 0;
		StringBuilder sb = new StringBuilder();
		for (String name : cfg.keySet()) {
			String value = cfg.get(name);
			sb.append("__(_|->_((# \"$" + name + "\"(.List{K})), (" + value + ")), ");
			items++;
		}
		sb.append("(.).Map");
		for (int i = 0; i < items; i++) {
			sb.append(")");
		}
		return sb.toString();
	}
}
