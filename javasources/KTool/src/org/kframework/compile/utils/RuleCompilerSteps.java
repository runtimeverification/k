package org.kframework.compile.utils;

import org.kframework.compile.transformers.*;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class RuleCompilerSteps extends CompilerSteps<Rule> {

	private SortCells cellSorter=null;
	private Set<Variable> vars;

	public Term getCellFragment(Variable v) {
		return cellSorter.getCellFragment(v);
	}

	public Set<Variable> getVars() {
		return vars;
	}

	public RuleCompilerSteps(Definition def) {
		super();
		this.add(new AddKCell());
		this.add(new AddTopCellRules());
		this.add(new ResolveAnonymousVariables());
		this.add(new ResolveSyntaxPredicates());
		this.add(new ResolveListOfK());
		this.add(new FlattenSyntax());
		ConfigurationStructureMap configurationStructureMap = new
				ConfigurationStructureMap();
		ConfigurationStructureVisitor cfgStrVisitor =
				new ConfigurationStructureVisitor(configurationStructureMap);
		def.accept(cfgStrVisitor);
		final ResolveContextAbstraction resolveContextAbstraction =
				new ResolveContextAbstraction(cfgStrVisitor.getMaxLevel(),
						configurationStructureMap);
		this.add(resolveContextAbstraction);
		this.add(new ResolveOpenCells());
		if (GlobalSettings.sortedCells) {
			cellSorter = new SortCells(configurationStructureMap);
			this.add(cellSorter);
		}
	}

	@Override
	public Rule compile(Rule def, String stepName) throws CompilerStepDone {
		CollectVariablesVisitor collectVars = new CollectVariablesVisitor();
		def.accept(collectVars);
		vars = new HashSet<Variable>();
		for (List<Variable> collectedVars : collectVars.getVars().values()) {
			vars.add(collectedVars.get(0));
		}
		return super.compile(def, stepName);
	}
}
