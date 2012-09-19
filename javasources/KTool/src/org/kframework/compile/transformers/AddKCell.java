package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Rule;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

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
