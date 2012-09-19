package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.k.ASTNode;
import org.kframework.k.Rule;
import org.kframework.visitors.CopyOnWriteTransformer;

public class AddKCell extends CopyOnWriteTransformer {

	public AddKCell() {
		super("Add K cell");
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
