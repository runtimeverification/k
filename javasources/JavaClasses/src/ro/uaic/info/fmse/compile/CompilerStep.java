package ro.uaic.info.fmse.compile;

import ro.uaic.info.fmse.k.Definition;

public interface CompilerStep {
	Definition compile(Definition def);
	String getName(); 
}
