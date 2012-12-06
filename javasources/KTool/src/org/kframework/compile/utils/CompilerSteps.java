package org.kframework.compile.utils;

import org.kframework.kil.Definition;
import org.kframework.kil.visitors.Transformer;

import java.util.ArrayList;
import java.util.List;


public class CompilerSteps extends BasicCompilerStep {

	List<CompilerStep> steps;

	public CompilerSteps() {
		steps = new ArrayList<CompilerStep>();
	}

	public CompilerSteps(List<CompilerStep> ts) {
		this.steps = new ArrayList<CompilerStep>(ts);
	}

	public void add(CompilerStep t) {
		steps.add(t);
	}

	public void add(Transformer t) {
		steps.add(new CompilerTransformerStep(t));
	}

	@Override
	public Definition compile(Definition def) {
		for (CompilerStep step : steps) {
			step.setSw(sw);
			def = step.compile(def);
		}
		return def;
	}

	@Override
	public String getName() {
		String result = "Aggregated transformers:\n";
		for (CompilerStep t : steps) {
			result+= "\t" + t.getName() + "\n";
		}
		return result;
	}

}
