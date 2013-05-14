package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddKCell extends CopyOnWriteTransformer {

	public AddKCell(DefinitionHelper definitionHelper) {
		super("Add K cell", definitionHelper);
	}
	
	@Override
	public ASTNode transform(Rule node) {
		if (MetaK.isAnywhere(node)) {
			return node;
		}
		String sort = node.getBody().getSort(definitionHelper);
		if (!sort.equals("K") && MetaK.isKSort(sort)) {
			return node;
		}
		node = node.shallowCopy();
		node.setBody(MetaK.kWrap(node.getBody()));
		return node;
	}
	
	@Override
	public ASTNode transform(Configuration cfg) throws TransformerException {
		if (!MetaK.getAllCellLabels(cfg.getBody(), definitionHelper).contains("k"))
		{
			Cell k = new Cell();
			k.setLabel("k");
			k.setEllipses(Ellipses.NONE);
			k.setContents(KSequence.EMPTY);
			
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
