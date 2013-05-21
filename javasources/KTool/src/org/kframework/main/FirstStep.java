package org.kframework.main;

import org.kframework.backend.Backend;
import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;

public class FirstStep extends BasicCompilerStep<Definition> {
	Backend backend;

	public FirstStep(Backend backend, Context context) {
		super(context);
		this.backend = backend;
	}

	@Override
	public Definition compile(Definition def, String stepName)
			throws CompilerStepDone {
		return backend.firstStep(def);
	}

	@Override
	public String getName() {
		return "FirstStep";
	}

	@Override
	public void setSw(Stopwatch sw) {
		// TODO Auto-generated method stub
		
	}
}
