package org.kframework.compile.utils;

import org.kframework.kil.Definition;
import org.kframework.kil.visitors.Visitor;
import org.kframework.utils.Stopwatch;

public class FunctionalAdaptor extends BasicCompilerStep<Definition> {

	private Visitor visitor;
	
	public FunctionalAdaptor(Visitor visitor) {
		this.visitor = visitor;
	}
	
	@Override
	public Definition compile(Definition def) {
		def.accept(visitor);
		return def;
	}

	@Override
	public String getName() {
		return visitor.getName();
	}
}
