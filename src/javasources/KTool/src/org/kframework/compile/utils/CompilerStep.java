package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.utils.Stopwatch;

public interface CompilerStep<T extends ASTNode> {
	T compile(T def, String stepName) throws CompilerStepDone;
	String getName();

	void setSw(Stopwatch sw);
}
