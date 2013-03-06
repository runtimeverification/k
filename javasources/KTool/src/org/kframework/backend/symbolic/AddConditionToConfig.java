package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.Terminal;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class AddConditionToConfig extends CopyOnWriteTransformer {

	static public String KCELL = "k";
	
	public AddConditionToConfig() {
		super("Add path condition to configuration");
	}


	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		Cell cell = new Cell();
		cell.setLabel(MetaK.Constants.pathCondition);
		cell.setEllipses(Ellipses.NONE);
		cell.setContents(Constant.TRUE);

		Term body = node.getBody();
		
		if (body instanceof Cell) {
			addCellNextToKCell((Cell) body, cell);
		}
		else if (body instanceof Bag)
		{
			// this should not happen because top cell is automatically added
		}
		
		node = node.shallowCopy();
		node.setBody(body);
		return node;
	}
	
	private boolean addCellNextToKCell(Cell cell, Cell toAdd) {
		
		Term contents = cell.getContents();
		if (contents instanceof Bag)
		{
			Bag content = (Bag) contents;
			List<Term> subCells = content.getContents();
			for (Term subCell : subCells)
			{
				if (subCell instanceof Cell && ((Cell) subCell).getLabel().equals(KCELL))
					// the cell kcell has been found as subcell of cell
					{
						subCells.add(toAdd);
						cell = cell.shallowCopy();
						cell.setContents(new Bag(subCells));
						return true;
					}
			}
			
			// none of the subcells of cell contains a cell labeled kcell
			for (Term subCell : subCells)
			{
				if (subCell instanceof Cell)
				{
					boolean added = addCellNextToKCell((Cell)subCell, toAdd);
					if (added) return true;
				}
			}
		}
		if (contents instanceof Cell)
		{
			Cell subCell = (Cell) contents;
			if (subCell.getLabel().equals(KCELL))
				// the cell kcell has been found as subcell of cell
				{
					List<Term> subCells = new ArrayList<Term>();
					subCells.add(subCell);
					subCells.add(toAdd);
					cell = cell.shallowCopy();
					cell.setContents(new Bag(subCells));
					return true;
				}
		
			// none of the subcells of cell contains a cell labeled kcell
			boolean added = addCellNextToKCell(subCell, toAdd);
			if (added) return true;
		}
		return false;
	}


	@Override
	public ASTNode transform(Module node) throws TransformerException {
		ASTNode result = super.transform(node);
		if (result == node) return node;
		if (result == null) { 
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.COMPILER, 
					"Expecting Module, but got null. Returning the untransformed module.", 
					getName(), node.getFilename(), node.getLocation()));					
			return node;
		}
		if (!(result instanceof Module)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Module, but got " + result.getClass() + " while transforming.", 
					node.getFilename(), node.getLocation()));	
			return node;
		}
		node = (Module) result;
		List<PriorityBlock> topCellBlocks = new ArrayList<PriorityBlock>();
		PriorityBlock topPriorityBlock = new PriorityBlock();
		List<ProductionItem> topTerminals = new ArrayList<ProductionItem>();
		topTerminals.add(new Terminal(MetaK.Constants.pathCondition));
		Production topProduction = new Production(new Sort("CellLabel"), topTerminals );
		topPriorityBlock.getProductions().add(topProduction);
		topCellBlocks.add(topPriorityBlock);
		Syntax topCellDecl = new Syntax(new Sort("CellLabel"), topCellBlocks );
		node.getItems().add(topCellDecl);
		return node;
	}

}
