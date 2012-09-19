package org.kframework.compile;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.CompilerStep;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Definition;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.Cell.Multiplicity;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class AddEval implements CompilerStep {

	@Override
	public Definition compile(Definition def) {
		Configuration cfg = MetaK.getConfiguration(def);
		Set<Variable> vars = MetaK.getVariables(cfg);
		
		ASTNode cfgCleanedNode = null;
		try {
			cfgCleanedNode = new ConfigurationCleaner().transform(cfg);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (!(cfgCleanedNode instanceof Configuration)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Configuration Cleaner failed.", 
					cfg.getFilename(), cfg.getLocation(), 0));
		}
		Configuration cfgCleaned = (Configuration)cfgCleanedNode;

		Rule ruleEval1 = new Rule();
		TermCons eval1Left = new TermCons("Bag", "Bag1EvalSyn");
		eval1Left.getContents().add(new Variable("M", "Map"));
		TermCons eval1Right = new TermCons("Bag", "Bag1EvalHelperSyn");
		TermCons updateMap = new TermCons("Map", "Map1UpdateMapWithMapSyn");
		updateMap.getContents().add(defaultMap(vars));
		updateMap.getContents().add(new Variable("M", "Map"));
		eval1Right.getContents().add(updateMap);
		ruleEval1.setBody(new Rewrite(eval1Left, eval1Right));

		Rule ruleEval2 = new Rule();
		TermCons eval2Left = new TermCons("Bag", "Bag1EvalHelperSyn");
		eval2Left.getContents().add(evalMap(vars));
		Term eval2Right = cfgCleaned.getBody();
		ruleEval2.setBody(new Rewrite(eval2Left, eval2Right));
		
		List<ModuleItem> rules = new ArrayList<ModuleItem>();
//		rules.add(syntaxBlock);
		rules.add(ruleEval1);
		rules.add(ruleEval2);
		Module module = def.getSingletonModule().addModuleItems(rules);

		return def.updateSingletonModule(module);
	}

	public Term defaultMapItem(Variable v) {
		MapItem item = new MapItem();
		item.setKey(MetaK.kWrapper(new Constant("String", "\"" + v.getName() + "\"")));
		item.setValue(MetaK.kWrapper(MetaK.defaultTerm(v)));
		return item;
	}
	
	public Term evalMapItem(Variable v) {
		MapItem item = new MapItem();
		item.setKey(MetaK.kWrapper(new Constant("String", "\"" + v.getName() + "\"")));
		item.setValue(MetaK.kWrapper(v));
		return item;
	}
	
	public Term defaultMap(Collection<Variable> vars) {
		Map map = new Map();
		for (Variable v : vars) {
			map.getContents().add(defaultMapItem(v));
		}
		return map;
	}
	
	public Term evalMap(Collection<Variable> vars) {
		Map map = new Map();
		for (Variable v : vars) {
			map.getContents().add(evalMapItem(v));
		}
		map.getContents().add(new Variable("Rest", "Map"));
		return map;
	}	
	
	
	class ConfigurationCleaner extends CopyOnWriteTransformer {
		
		public ConfigurationCleaner() {
			super("Configuration Cleaner");
			// TODO Auto-generated constructor stub
		}

		@Override
		public ASTNode transform(Cell node) throws TransformerException {
			if (node.getMultiplicity() == Multiplicity.ANY || node.getMultiplicity() == Multiplicity.MAYBE) {
				if (MetaK.getVariables(node).isEmpty()) {
					return null;
				}
			}

			ASTNode result = super.transform(node);
			if (result == null) return null;
			if (!(result instanceof Cell)) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
						KExceptionGroup.INTERNAL, 
						"Expecting Cell, but got " + node.getClass() + " in Configuration Cleaner.", 
						node.getFilename(), node.getLocation(), 0));
			}
			if (result == node) {
				node = node.shallowCopy();
			} else node = (Cell) result;
			node.setDefaultAttributes();
			node.setElipses("none");
			return node;
		}

	}


	@Override
	public String getName() {
		return "Add eval construct";
	}
}
