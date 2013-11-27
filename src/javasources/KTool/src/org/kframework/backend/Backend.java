package org.kframework.backend;

import org.kframework.compile.utils.CompilerSteps;
import org.kframework.kil.Definition;

import java.io.IOException;

public interface Backend {
	public void run(Definition definition) throws IOException;

	public String getDefaultStep();

	Definition firstStep(Definition def);

	Definition lastStep(Definition def);

	public boolean autoinclude();

	public CompilerSteps<Definition> getCompilationSteps();
}
