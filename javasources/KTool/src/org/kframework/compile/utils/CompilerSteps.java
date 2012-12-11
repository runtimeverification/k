package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.visitors.Transformer;

import java.util.ArrayList;
import java.util.List;


public class CompilerSteps<T extends ASTNode> extends BasicCompilerStep<T> {

	List<CompilerStep<T>> steps;

	public CompilerSteps() {
		steps = new ArrayList<CompilerStep<T>>();
	}

	public CompilerSteps(List<CompilerStep<T>> ts) {
		this.steps = new ArrayList<CompilerStep<T>>(ts);
	}

	public void add(CompilerStep<T> t) {
		steps.add(t);
	}

	public void add(Transformer t) {
		steps.add(new CompilerTransformerStep<T>(t));
	}

	@Override
	public T compile(T def) {
		for (CompilerStep<T> step : steps) {
			step.setSw(sw);
			def = step.compile(def);
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
