package org.kframework.compile.utils;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.Stack;

/**
 * Visitor populating the configurationStructureMap of a given Context object.
 * @see ConfigurationStructureMap for additional info about this structure.
 */
public class ConfigurationStructureVisitor extends BasicVisitor {

    Stack<ConfigurationStructure> ancestors = new Stack<ConfigurationStructure>();

	private ConfigurationStructureMap config;
	private int maxLevel = 0;

	public ConfigurationStructureVisitor(Context context) {
		super(context);
		this.config = context.getConfigurationStructureMap();
		this.config.clear();
	}

	@Override
	public void visit(Configuration node) {
		Term t = node.getBody();
		Cell top = new Cell();
		top.setLabel(MetaK.Constants.generatedCfgAbsTopCellLabel);
		top.setId(MetaK.Constants.generatedCfgAbsTopCellLabel);
		top.setContents(t);
		top.accept(this);
	}
	
	@Override
	public void visit(Cell node) {
		ConfigurationStructure cfg = new ConfigurationStructure();
		cfg.multiplicity = node.getMultiplicity();
		cfg.id = node.getId();
		cfg.cell = node;
		if (!ancestors.empty()) {
			ConfigurationStructure parent = ancestors.peek();
			cfg.level = parent.level+1;
			cfg.parent = parent;
			if (cfg.level > maxLevel) maxLevel = cfg.level;
			parent.sons.put(cfg.id, cfg);
		}
		ancestors.push(cfg);
		super.visit(node);
		ancestors.pop();
		config.put(cfg.id, cfg);
	}
	
	@Override
	public void visit(org.kframework.kil.Context node) {
	}

	@Override
	public void visit(Syntax node) {
	}

	@Override
	public void visit(Rule node) {
	}

	public int getMaxLevel() {
		return maxLevel;
	}
}
