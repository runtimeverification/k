package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Definition;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;


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
					def.getFilename(), def.getLocation()));					
		}
		return (Definition) result;
	}

	@Override
	public String getName() {
		return t.getName();
	}

}
