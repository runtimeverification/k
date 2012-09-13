package ro.uaic.info.fmse.compile.transformers;

import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

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
