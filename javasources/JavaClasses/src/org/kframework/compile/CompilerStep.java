package org.kframework.compile;

import org.kframework.k.Definition;

public interface CompilerStep {
	Definition compile(Definition def);
	String getName(); 
}
