package org.kframework.compile.transformers;

import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Cell.Multiplicity;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class ResolveDefaultTerms extends CopyOnWriteTransformer {
	
	private Map<String, ConfigurationStructure> config;

	public ResolveDefaultTerms(Context context) {
		super("Resolve Default Terms", context);
        config = context.getConfigurationStructureMap();
	}
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		if (MetaK.isAnywhere(node)) return node;
		return super.transform(node);
	}
	
	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		ASTNode right = node.getRight().accept(new DefaultTermsResolver(context));
		if (right != node.getRight()) {
			node = node.shallowCopy();
			node.setRight((Term)right, context);
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
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return node;
	}
	
	
	public class DefaultTermsResolver extends CopyOnWriteTransformer {
		
		public DefaultTermsResolver(Context context) {
			super("Default Terms Resolver", context);
		}
		
		@Override
		public ASTNode transform(Cell node) throws TransformerException {
			Cell cell = (Cell) super.transform(node);
			if (cell.getEllipses() == Ellipses.NONE) return cell;
			cell = cell.shallowCopy();
			cell.setCellAttributes(new HashMap<String, String>(cell.getCellAttributes()));
			cell.setEllipses(Ellipses.NONE);
			ConfigurationStructure cellStr = config.get(cell.getId());
			if (cellStr.sons.isEmpty()) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
						KExceptionGroup.COMPILER, 
						"Cell " + node + " is a leaf in the configuration and it's not closed in the RHS.", 
						getName(), node.getFilename(), node.getLocation()));								
				
				return cell;
			}
			List<Cell> sons = MetaK.getTopCells(cell.getContents(), context);
			Map<String, ConfigurationStructure> potentialSons = new HashMap<String, ConfigurationStructure>(cellStr.sons);
			
			for (Cell son : sons) {
				ConfigurationStructure sonCfg = potentialSons.get(son.getId());
				if (sonCfg != null && (sonCfg.multiplicity == Multiplicity.ONE || sonCfg.multiplicity == Multiplicity.SOME)) 
						potentialSons.remove(son.getId());
			}
			
			if (potentialSons.isEmpty()) return cell;
			
			Bag bag;
			if (cell.getContents() instanceof Bag) {
				bag = (Bag) cell.getContents().shallowCopy();
				bag.setContents(new ArrayList<Term>(bag.getContents()));
			} else {
				bag = new Bag();
				bag.getContents().add(cell.getContents());
			}
			boolean change = false;
			for (ConfigurationStructure sonCfg : potentialSons.values()) {
				if (sonCfg.multiplicity == Multiplicity.ONE || sonCfg.multiplicity == Multiplicity.SOME) {
					Cell son = sonCfg.cell.shallowCopy();
					son.setCellAttributes(new HashMap<String, String>());
					if (! sonCfg.sons.isEmpty()) { 
						son.setContents(new Bag());
						son.setEllipses(Ellipses.BOTH);
						son = (Cell)transform(son);
					}
					bag.getContents().add(son);
					change = true;
				}
			}
			if (change) {
				cell.setContents(bag);
			}
			return cell;
		}


	}

}
