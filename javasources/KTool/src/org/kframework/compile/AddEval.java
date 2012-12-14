package org.kframework.compile;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Cell.Multiplicity;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;


public class AddEval extends BasicCompilerStep<Definition> {

	@Override
	public Definition compile(Definition def, String stepName) {
		Configuration cfg = MetaK.getConfiguration(def);
		Set<Variable> vars = MetaK.getVariables(cfg);
		
		ASTNode cfgCleanedNode = null;
		try {
			cfgCleanedNode = new ConfigurationCleaner().transform(cfg);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Configuration cfgCleaned;
		if (cfgCleanedNode==null) {
			cfgCleaned = new Configuration();
			cfgCleaned.setBody(new Empty(MetaK.Constants.Bag));
		} else {
			if (!(cfgCleanedNode instanceof Configuration)) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
						KExceptionGroup.INTERNAL,
						"Configuration Cleaner failed.",
						cfg.getFilename(), cfg.getLocation()));
			}
			cfgCleaned = (Configuration)cfgCleanedNode;
		}

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

			if (result == node) {
				node = node.shallowCopy();
			} else {
				if (!(result instanceof Cell)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
							KExceptionGroup.INTERNAL,
							"Expecting Cell, but got " + node.getClass() + " in Configuration Cleaner.",
							getName(), node.getFilename(), node.getLocation()));
				} else	node = (Cell) result;
			}
			node.setDefaultAttributes();
			node.setEllipses(Ellipses.NONE);
			return node;
		}

	}


	@Override
	public String getName() {
		return "Add eval construct";
	}
}
