package org.kframework.compile.utils;

import java.util.HashMap;
import java.util.Map;
import java.util.Stack;

import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.Cell.Multiplicity;
import org.kframework.kil.visitors.BasicVisitor;

public class ConfigurationStructureVisitor extends BasicVisitor {
	
	public class ConfigurationStructure {
		public Cell cell;
		public String id;
		public ConfigurationStructure parent = null;
		public Map<String,ConfigurationStructure> sons = new HashMap<String, ConfigurationStructure>();
		public Multiplicity multiplicity;
		public int level = 0;
	}

	Stack<ConfigurationStructure> ancestors = new Stack<ConfigurationStructureVisitor.ConfigurationStructure>();

	private Map<String, ConfigurationStructureVisitor.ConfigurationStructure> config = new HashMap<String, ConfigurationStructureVisitor.ConfigurationStructure>();
	private int maxLevel = 0;
	
	
	@Override
	public void visit(Configuration node) {
		Term t = node.getBody();
		Cell top = new Cell();
		top.setLabel("___CONTEXT_ABSTRACTION_TOP_CELL___");
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
	public void visit(Context node) {
	}

	@Override
	public void visit(Syntax node) {
	}

	@Override
	public void visit(Rule node) {
	}

	public Map<String, ConfigurationStructureVisitor.ConfigurationStructure> getConfig() {
		return config;
	}

	public int getMaxLevel() {
		return maxLevel;
	}
}