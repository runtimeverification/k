package org.kframework.backend.symbolic.rl;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.compile.utils.RuleCompilerSteps;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.K;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

public class ResolveRLFile extends CopyOnWriteTransformer {

	public ResolveRLFile(DefinitionHelper definitionHelper) {
		super("Parse RL input file", definitionHelper);

		String[] rrls = FileUtil.getFileContent(GlobalSettings.CHECK).split(
				"reachability-rule");
		List<String> rrs = new ArrayList<String>();
		for (int i = 0; i < rrls.length; i++)
		{
			if (!rrls[i].trim().equals(""))
				rrs.add(rrls[i]);
		}
//		ParseRulesFilter prf = new ParseRulesFilter();
		for (String s : rrs) {
			try {
				System.out.println("Parsing: |" + s + "|");
				K.compiled_def = org.kframework.krun.Main.initOptions(K.userdir);
				if (K.compiled_def != null) {
					int index = K.compiled_def.indexOf("-kompiled");
					K.k_definition = K.compiled_def.substring(0, index);
				}
				
				definitionHelper.kompiled = new File(K.compiled_def);
				System.out.println("TBL: " + new File(definitionHelper.kompiled.getCanonicalPath()
								+ "/ground/Concrete.tbl").exists());
				org.kframework.parser.concrete.KParser
						.ImportTblGround(definitionHelper.kompiled.getCanonicalPath()
								+ "/ground/Concrete.tbl");
				ASTNode out = DefinitionLoader.parseCmdString(s, "", "generated", definitionHelper);
				try {
					out = new RuleCompilerSteps(K.definition, definitionHelper).compile((Rule) out, null);
				} catch (CompilerStepDone e) {
					out = (ASTNode) e.getResult();
				}
				out = ((Rule) out).getBody();
			} catch (TransformerException e) {
				e.printStackTrace();
			} catch (IOException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
		}

		System.out.println("RL not supported yet!");
	}
}
