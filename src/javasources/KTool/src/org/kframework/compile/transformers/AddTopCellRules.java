package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;


public class AddTopCellRules extends CopyOnWriteTransformer {

	public AddTopCellRules(Context context) {
		super("Add top cell for rules", context);
	}
	
	@Override
	public ASTNode transform(Rule node) {
		if (MetaK.isAnywhere(node)) return node;
		if (!MetaK.hasCell(node.getBody(), context)) return node;
		node = node.shallowCopy();
		node.setBody(MetaK.wrap(node.getBody(),MetaK.Constants.generatedTopCellLabel,Ellipses.BOTH));
		return node;
	}
	
	@Override
	public ASTNode transform(Configuration node) {
		return node;
	}
	
	@Override
	public ASTNode transform(org.kframework.kil.Context node) {
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) {
		return node;
	}

}
