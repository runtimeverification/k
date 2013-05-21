package org.kframework.compile.utils;

import org.kframework.kil.Definition;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.Visitor;

public class FunctionalAdaptor extends BasicCompilerStep<Definition> {

	private Visitor visitor;

	public FunctionalAdaptor(Visitor visitor, Context context) {
		super(context);
		this.visitor = visitor;
	}

	@Override
	public Definition compile(Definition def, String stepName) {
		def.accept(visitor);
		return def;
	}

	@Override
	public String getName() {
		return visitor.getName();
	}
}
