package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.HashMap;

public class ResolveOpenCells extends CopyOnWriteTransformer {

	public ResolveOpenCells() {
		super("Resolve Open Cells");
	}
	
	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		node = (Cell) super.transform(node);
		Ellipses ellipses = node.getEllipses();
		if (ellipses == Ellipses.NONE) 
			return node;
		node = node.shallowCopy();
		node.setCellAttributes(new HashMap<String, String>(node.getCellAttributes()));
		node.setEllipses(Ellipses.NONE);
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
						"Expecting a collection item here but got " + node.getContents() + " which is of sort " + sort, getName(), 
						node.getFilename(), node.getLocation()));
								
			}
		}
		node.setContents(col);
		if (ellipses == Ellipses.BOTH && sort != KSort.K && sort != KSort.List) {
			ellipses = Ellipses.RIGHT;
		}
		if (ellipses == Ellipses.BOTH || ellipses == Ellipses.LEFT) {
			col.getContents().add(0, Variable.getFreshVar(sort.toString()));
		}
		if (ellipses == Ellipses.BOTH || ellipses == Ellipses.RIGHT) {
			col.getContents().add(Variable.getFreshVar(sort.toString()));
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
