package ro.uaic.info.fmse.compile;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.k.Cell.Multiplicity;
import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Map;
import ro.uaic.info.fmse.k.MapItem;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.ModuleItem;
import ro.uaic.info.fmse.k.Rewrite;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

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
