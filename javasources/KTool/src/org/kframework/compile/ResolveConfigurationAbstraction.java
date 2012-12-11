package org.kframework.compile;

import org.kframework.compile.transformers.ResolveContextAbstraction;
import org.kframework.compile.transformers.ResolveDefaultTerms;
import org.kframework.compile.utils.CompilerSteps;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.compile.utils.ConfigurationStructureVisitor;
import org.kframework.kil.Definition;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/6/12
 * Time: 12:27 PM
 */
public class ResolveConfigurationAbstraction extends CompilerSteps<Definition> {
	@Override
	public Definition compile(Definition def) {
		ConfigurationStructureVisitor cfgStrVisitor = new ConfigurationStructureVisitor();
		def.accept(cfgStrVisitor);
		int cfgMaxLevel = cfgStrVisitor.getMaxLevel();
		ConfigurationStructureMap cfgStr = cfgStrVisitor.getConfig();
		add(new ResolveContextAbstraction(cfgMaxLevel, cfgStr));
		add(new ResolveDefaultTerms(cfgStr));
		return super.compile(def);
	}
}
