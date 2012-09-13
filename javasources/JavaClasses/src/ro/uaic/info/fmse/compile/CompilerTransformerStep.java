package ro.uaic.info.fmse.compile;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.visitors.Transformer;

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
