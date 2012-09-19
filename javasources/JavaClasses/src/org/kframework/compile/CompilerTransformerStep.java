package org.kframework.compile;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Definition;
import org.kframework.visitors.Transformer;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class CompilerTransformerStep implements CompilerStep {
	
	Transformer t;
	
	public CompilerTransformerStep(Transformer t) {
		this.t = t;
	}

	@Override
	public Definition compile(Definition def) {
		ASTNode result = null;
		try {
			result = def.accept(t);
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		if (!(result instanceof Definition)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Definition, but got " + result.getClass() 
					+ " while applying" + getName() + ".", 
					def.getFilename(), def.getLocation(), 0));					
		}
		return (Definition) result;
	}

	@Override
	public String getName() {
		return t.getName();
	}

}
