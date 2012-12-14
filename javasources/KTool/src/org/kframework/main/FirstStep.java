package org.kframework.main;

import org.kframework.compile.utils.BasicCompilerStep;
import org.kframework.compile.utils.CompilerStepDone;
import org.kframework.kil.Definition;
import org.kframework.utils.Stopwatch;

public class FirstStep extends BasicCompilerStep<Definition> {

	@Override
	public Definition compile(Definition def, String stepName)
			throws CompilerStepDone {
		return def;
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
