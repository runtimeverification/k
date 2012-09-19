package org.kframework.compile.utils;

import org.kframework.kil.Definition;

public interface CompilerStep {
	Definition compile(Definition def);
	String getName(); 
}
