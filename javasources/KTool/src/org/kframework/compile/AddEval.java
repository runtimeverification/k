package org.kframework.compile;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Definition;
import org.kframework.kil.Empty;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class AddEval extends BasicCompilerStep<Definition> {

	public AddEval(DefinitionHelper definitionHelper) {
		super(definitionHelper);
	}
	
	@Override
	public Definition compile(Definition def, String stepName) {
		Configuration cfg = MetaK.getConfiguration(def, definitionHelper);
		Set<Variable> vars = MetaK.getVariables(cfg, definitionHelper);

		ASTNode cfgCleanedNode = null;
		try {
			cfgCleanedNode = new ConfigurationCleaner(definitionHelper).transform(cfg);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		Configuration cfgCleaned;
		if (cfgCleanedNode == null) {
			cfgCleaned = new Configuration();
			cfgCleaned.setBody(Bag.EMPTY);
		} else {
			if (!(cfgCleanedNode instanceof Configuration)) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Configuration Cleaner failed.", getName(), cfg.getFilename(), cfg.getLocation()));
			}
			cfgCleaned = (Configuration) cfgCleanedNode;
		}

		Rule ruleEval1 = new Rule();
		TermCons eval1Left = new TermCons("Bag", "Bag1EvalSyn");
		eval1Left.getContents().add(new Variable("M", "Map"));
		TermCons eval1Right = new TermCons("Bag", "Bag1EvalHelperSyn");
		TermCons updateMap = new TermCons("Map", "Map1UpdateMapWithMapSyn");
		updateMap.getContents().add(defaultMap(vars));
		updateMap.getContents().add(new Variable("M", "Map"));
		eval1Right.getContents().add(updateMap);
		ruleEval1.setBody(new Rewrite(eval1Left, eval1Right, definitionHelper));

		Rule ruleEval2 = new Rule();
		TermCons eval2Left = new TermCons("Bag", "Bag1EvalHelperSyn");
		eval2Left.getContents().add(evalMap(vars));
		Term eval2Right = cfgCleaned.getBody();
		ruleEval2.setBody(new Rewrite(eval2Left, eval2Right, definitionHelper));

		List<ModuleItem> rules = new ArrayList<ModuleItem>();
		// rules.add(syntaxBlock);
		rules.add(ruleEval1);
		rules.add(ruleEval2);
		Module module = def.getSingletonModule().addModuleItems(rules);

		return def.updateSingletonModule(module);
	}

	public Term defaultMapItem(Variable v) {
		MapItem item = new MapItem();
		item.setKey(definitionHelper.kWrapper(StringBuiltin.of(v.getName())));
		item.setValue(definitionHelper.kWrapper(MetaK.defaultTerm(v, definitionHelper)));
		return item;
	}

	public Term evalMapItem(Variable v) {
		MapItem item = new MapItem();
		item.setKey(definitionHelper.kWrapper(StringBuiltin.of(v.getName())));
		item.setValue(definitionHelper.kWrapper(v));
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

	@Override
	public String getName() {
		return "Add eval construct";
	}
}
