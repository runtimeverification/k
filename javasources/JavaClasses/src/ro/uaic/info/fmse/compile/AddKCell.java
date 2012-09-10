package ro.uaic.info.fmse.compile;

import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

public class AddKCell extends CopyOnWriteTransformer implements CompilerStep {

	@Override
	public Definition compile(Definition def) {
		ASTNode result = null;
		try {
			result = def.accept(this);
		} catch (TransformerException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		if (result == null) { 
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.COMPILER, 
					"Expecting definition, but got null while adding the <k> cell. Returning the definition untransformed.", 
					def.getFilename(), def.getLocation(), 0));					
			return def;
		}
		if (!(result instanceof Definition)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + result.getClass() + " while adding the <k> cell. Returning the definition untransformed.", 
					def.getFilename(), def.getLocation(), 0));					
		}
		return (Definition) result;
	}

	@Override
	public String getName() {
		return "Add <k> cell";
	}
	
	@Override
	public ASTNode transform(Rule node) {
		if (MetaK.isAnywhere(node)) return node;
		String sort = node.getBody().getSort();
		if (!sort.equals("K") && MetaK.isKSort(sort))
			return node;
		node = node.shallowCopy();
		node.setBody(MetaK.kWrap(node.getBody()));
		return node;
	}

}
