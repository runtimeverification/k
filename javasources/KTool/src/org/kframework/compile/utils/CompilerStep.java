package org.kframework.compile.utils;

import org.kframework.kil.Definition;
import org.kframework.utils.Stopwatch;

public interface CompilerStep {
	Definition compile(Definition def);
	String getName();

	void setSw(Stopwatch sw);
}
