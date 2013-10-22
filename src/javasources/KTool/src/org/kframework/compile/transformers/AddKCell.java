package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class AddKCell extends CopyOnWriteTransformer {
	/*
	 * Stores the list of cells that contain komputations. By default, contains only the "k" cell.
	 */
	protected java.util.List<String> komputationCells;

	/*
	 * Used to remember for each module the rules that need to be added.
	 */
	protected java.util.List<ModuleItem> newRules;
	
	public AddKCell(Context context) {
		super("Add K cell", context);
		this.komputationCells = new ArrayList<String>();
		if (context.getKomputationCells() == null) {
			this.komputationCells.add("k");
		} else {
			this.komputationCells = context.getKomputationCells();
		}
		assert !this.komputationCells.isEmpty();
	}

	@Override
	public ASTNode transform(Module module) throws TransformerException {
		newRules = new ArrayList<ModuleItem>();
		Module newModule = (Module)super.transform(module);
		Module returnModule;
		if (newRules.isEmpty()) {
			returnModule = newModule;
		} else {
			returnModule = newModule.shallowCopy();		
			returnModule = returnModule.addModuleItems(newRules);
		}
		return returnModule;
	}

	@Override
	public ASTNode transform(Rule node) {
		if (MetaK.isAnywhere(node)) {
			return node;
		}

		if (!MetaK.isComputationSort(node.getBody().getSort())) {
			return node;
		}
		node = node.shallowCopy();
		for (int i = 1; i < komputationCells.size(); ++i) {
			// first all other rules are scheduled to be added
			Rule newRule = node.shallowCopy();
			newRule.setBody(MetaK.kWrap(node.getBody(), this.komputationCells.get(i)));
			newRules.add(newRule);
		}
		assert !this.komputationCells.isEmpty();
		node.setBody(MetaK.kWrap(node.getBody(), this.komputationCells.get(0))); // then first rule replaces older rule
		
		return node;
	}

    @Override
	public ASTNode transform(Configuration cfg) throws TransformerException {
		if (!intersects(MetaK.getAllCellLabels(cfg.getBody(), context), komputationCells))
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

	private static boolean intersects(List<String> l1, List<String> l2) {
		for (String s1 : l1) {
			if (l2.contains(s1)) {
				return true;
			}
		}
		return false;
	}
}
