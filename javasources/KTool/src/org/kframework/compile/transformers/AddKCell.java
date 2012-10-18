package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Configuration;
import org.kframework.kil.Empty;
import org.kframework.kil.Rule;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

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
	
	@Override
	public ASTNode transform(Configuration cfg) throws TransformerException {
		if (!MetaK.getAllCellLabels(cfg.getBody()).contains("k"))
		{
			Cell k = new Cell();
			k.setLabel("k");
			k.setEllipses(Ellipses.NONE);
			k.setContents(new Empty("K"));
			
			cfg = cfg.shallowCopy();

			Bag bag;
			if (cfg.getBody() instanceof Bag) {
				bag = (Bag) cfg.getBody().shallowCopy();
			} else {
				bag = new Bag();
				bag.getContents().add(cfg.getBody());
			}
			cfg.setBody(bag);
			bag.getContents().add(k);
		}
		
		return cfg;
	}

}
