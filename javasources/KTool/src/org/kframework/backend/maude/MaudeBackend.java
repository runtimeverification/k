package org.kframework.backend.maude;

import org.apache.commons.lang3.StringEscapeUtils;
import org.kframework.backend.BasicBackend;
import org.kframework.kil.Attribute;
import org.kframework.kil.Definition;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.Syntax;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.IOException;
import java.util.HashSet;
import java.util.Map;

public class MaudeBackend extends BasicBackend {

	public MaudeBackend(Stopwatch sw) {
		super(sw);
	}

	@Override
	public void run(Definition definition) throws IOException {
		MaudeFilter maudeFilter = new MaudeFilter();
		definition.accept(maudeFilter);

		final String mainModule = definition.getMainModule();
		String maudified = maudeFilter.getResult().replaceFirst(mainModule, mainModule + "-BASE");

		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/base.maude", maudified);
		if (GlobalSettings.verbose)
			sw.printIntermediate("Generating Maude file");
		
		String consTable = getLabelTable(definition);
		FileUtil.saveInFile(DefinitionHelper.dotk.getAbsolutePath() + "/consTable.txt", consTable);
	}
	
	private String getLabelTable(Definition def) {
		StringBuilder b = new StringBuilder();
		/*
		b.append("# Each line has the SDF cons label, a literal tab, a space or * to mark preferred productions,\n"+
		         "# then P followed by the klabel for ordinary productions, a B for brackets,\n"+
				 "# or L followed by the klabel, a tab, and the separator.\n"+
		         "# strings escaped with \\t for tabs and \\n for newlines. # is comment to end of line");
		 */
		for (Map.Entry<String,Production> e : DefinitionHelper.conses.entrySet()) {
			String cons = e.getKey();
			Production p = e.getValue();
			b.append(StringEscapeUtils.escapeJava(cons));
			b.append('\t');
			if (p.containsAttribute("prefer")) {
				b.append('*');
			} else {
				b.append(' ');
			}
			if (p.isListDecl()) {
				b.append('L');
				b.append(StringEscapeUtils.escapeJava(p.getKLabel()));
				b.append('\t');
				b.append(StringEscapeUtils.escapeJava(((UserList)p.getItems().get(0)).getSeparator()));
			} else if (p.containsAttribute("bracket")) {
				b.append('B');
			} else {
				b.append('P');
				b.append(StringEscapeUtils.escapeJava(p.getKLabel()));
			}
			b.append('\n');			
		}
		return b.toString();
	}

	@Override
	public String getDefaultStep() {
		return "LastStep";
	}
}
