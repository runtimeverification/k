package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.Transformer;

import java.util.ArrayList;
import java.util.List;


public class CompilerSteps<T extends ASTNode> extends BasicCompilerStep<T> {

	List<CompilerStep<T>> steps;

	public CompilerSteps(DefinitionHelper definitionHelper) {
		super(definitionHelper);
		steps = new ArrayList<CompilerStep<T>>();
	}

	public CompilerSteps(List<CompilerStep<T>> ts, DefinitionHelper definitionHelper) {
		super(definitionHelper);
		this.steps = new ArrayList<CompilerStep<T>>(ts);
	}

	public void add(CompilerStep<T> t) {
		steps.add(t);
	}

	public void add(Transformer t) {
		steps.add(new CompilerTransformerStep<T>(t, definitionHelper));
	}

	@Override
	public T compile(T def, String stepName) throws CompilerStepDone {
		for (CompilerStep<T> step : steps) {
			step.setSw(sw);
			def = step.compile(def, stepName);
			if (step.getName().equals(stepName)) {
				throw new CompilerStepDone(def);
			}
		}
		return def;
	}

	@Override
	public String getName() {
		String result = "Aggregated transformers:\n";
		for (CompilerStep<T> t : steps) {
			result+= "\t" + t.getName() + "\n";
		}
		return result;
	}

}
