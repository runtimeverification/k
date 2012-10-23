package org.kframework.compile.transformers;

import java.util.ArrayList;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Collection;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.KSort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class ResolveOpenCells extends CopyOnWriteTransformer {

	public ResolveOpenCells() {
		super("Resolve Open Cells");
	}
	
	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		if (node.getEllipses() == Ellipses.NONE) 
			return node;
		node = node.shallowCopy();
		KSort sort = KSort.getKSort(node.getContents().getSort()).mainSort();
		Collection col;
		if (node.getContents() instanceof Collection) {
			col = (Collection) node.getContents().shallowCopy();
			col.setContents(new ArrayList<Term>(col.getContents()));
		} else {
			col = MetaK.createCollection(node.getContents(), sort);
			if (col == null) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
						KExceptionGroup.COMPILER, 
						"Expecting a collection item here but got " + node.getContents() + " which is of sort " + sort + 
						"Compilation Phase: " + getName(), 
						node.getFilename(), node.getLocation()));
								
			}
		}
		node.setContents(col);
		if (node.getEllipses() == Ellipses.BOTH) {
			
		}
		return node;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Context node) throws TransformerException {
		return node;
	}

}
