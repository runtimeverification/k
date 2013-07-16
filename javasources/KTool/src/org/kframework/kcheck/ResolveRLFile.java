package org.kframework.kcheck;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.parser.DefinitionLoader;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

public class ResolveRLFile extends CopyOnWriteTransformer {

	List<ASTNode> reachabilityRules = new ArrayList<ASTNode>();
	
	public ResolveRLFile(Context context) {
		super("Parse RL input file", context);

		String[] rrls = FileUtil.getFileContent(GlobalSettings.CHECK).split(
				"reachability-rule");
		List<String> rrs = new ArrayList<String>();
		for (int i = 0; i < rrls.length; i++)
		{
			if (!rrls[i].trim().equals(""))
				rrs.add(rrls[i]);
		}
		for (String s : rrs) {
//			System.out.println("Sentence to parse: " + s + "\n");
			
			try {
				ASTNode r = DefinitionLoader.parseSentence(s, GlobalSettings.CHECK, context);
				reachabilityRules.add(r);
			} catch (TransformerException e) {
				e.printStackTrace();
			}
		}
	}

	public List<ASTNode> getReachabilityRules() {
		return reachabilityRules;
	}
}
