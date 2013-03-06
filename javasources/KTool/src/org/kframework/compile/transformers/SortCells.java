package org.kframework.compile.transformers;

import org.kframework.compile.ResolveConfigurationAbstraction;
import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;
import java.util.List;
import java.util.Map;

/*
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 2/6/13
 * Time: 6:03 PM
 */

/**
 * Sort the cells in the rules so that they match the configuration structure.
 * This is meant as an intermediate step towards flattening the structure of
 * the configuration.
 *
 * Prerequisites:  Assuming that ResolveConfigurationAbstraction has run,
 * that the rewrites have been already pushed to the
 * top, and that all rules are completed to the top (or at least,
 * they have a cell at the top of both their lhs and rhs.
 */
public class SortCells extends CopyOnWriteTransformer {

	// We need a pointer to the ResolveConfigurationAbstraction step to
	// extract the configuration structure from it, which is only available
	// after the step has run.
	private ResolveConfigurationAbstraction resolveConfigurationAbstraction;
	// Mapping each variable in a cell to the list of variables it must be
	// split to.  We keep that list as a cell, because it will be used almost
	// as-is to generate the corresponding cell fragment.
	// They are rule-scoped
	private Map<Variable,Cell> variables
			= new HashMap<Variable, Cell>();

	SortCells() {
		super("SortCells");
	}

	/**
	 * Initializes the object. Requires a reference to the
	 * ResolveConfigurationAbstraction compilation step which will be used
	 * during the transformation to retrieve a ConfigurationStructureMap.
	 *
	 * @param resolveConfigurationAbstraction
	 */
	public SortCells(ResolveConfigurationAbstraction resolveConfigurationAbstraction) {
		this();
		this.resolveConfigurationAbstraction = resolveConfigurationAbstraction;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Context node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}

	/**
	 * Sorts the cells of a rule according to their order in the configuration.
	 *
	 * SortLeftCells sorts cells in the lhs and populates the variables map.
	 * SortRightCells sort cells in the rhs updating the cell variables
	 * accordingly.
	 * ResolveRemainingVariables handles cell variables used outside cells.
	 *
	 * @param node
	 * @return the new rule with sorted cells
	 * @throws TransformerException
	 */
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		variables.clear();  // reset the variables map
		Term body = node.getBody();
		if (!(body instanceof Rewrite)) {
			GlobalSettings.kem.register(new KException(KException
					.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
					"All rules should have rewrite at top by now", getName(),
					node.getFilename(), node.getLocation()));
		}
		Rewrite rew = (Rewrite)body;
		Term left = (Term) rew.getLeft().accept(
				new SortLeftCells());
		Term right = (Term) rew.getRight().accept(
				new SortRightCells());
		rew = rew.shallowCopy();
		rew.setLeft(left);
		rew.setRight(right);
		node = node.shallowCopy();
		node.setBody(rew);
		return node.accept(new ResolveRemainingVariables());
	}

	/**
	 * Meant for sorting the cells in the lhs and figuring out how a cell
	 * variable must be split in multiple pieces to account for each
	 * potential cell it could stand for.
	 */
	private class SortLeftCells extends SortCellCells {
		public SortLeftCells() {
			super("Sorting Left Cells");
		}

		/**
		 * Adding the new variable generated to the list of renamed vars.
		 * @param newVar
		 */
		@Override
		void updateRenamedVars(Variable newVar) {
			if (framingVariable != null) {
				renamedVars.add(newVar);
			}
		}

		/**
		 * Map the current cell variable to its replacement variables in the
		 * variables map.  A cell is used to wrap those variables to make it
		 * easier to generate a cell fragment later.
		 * @param node
		 * @return true
		 */
		@Override
		boolean initializeRenamedVars(Cell node) {
			if (framingVariable != null) {
				renamedVars = new ArrayList<Term>();
				Cell node1 = node.shallowCopy();
				node1.setContents(new Bag(renamedVars));
				variables.put(framingVariable, node1);
			} else {
				renamedVars = null;
			}
			return true;
		}

		/**
		 * Generates the appropriate variable for the cell position under
		 * consirderation depending on whether cells on the current position
		 * already exists in this cell and on the multiplicity of the cell.
		 * @param cellsExist
		 * @param multiplicity
		 * @return  the replacement variable, or null if none needed.
		 */
		@Override
		Variable getReplacementVariable(boolean cellsExist, Cell.Multiplicity multiplicity) {
			if (framingVariable == null) return null;
			Variable newVar = null;
			if (cellsExist) {
				if (multiplicity == Cell.Multiplicity.ANY ||
						multiplicity == Cell.Multiplicity.SOME) {
					newVar = MetaK.getFreshVar(MetaK.Constants.Bag);
				}
			} else {
				if (multiplicity == Cell.Multiplicity.ONE) {
					newVar = MetaK.getFreshVar(MetaK.Constants.BagItem);
				} else {
					newVar = MetaK.getFreshVar(MetaK.Constants.Bag);
				}
			}
			return newVar;
		}
	}

	/**
	 * Class for sorting the cells in the rhs and replacing the cell
	 * variables with the appropriate variables computed in the variables map.
	 */
	private class SortRightCells extends SortCellCells {
		// holds the index in the renamedVars list. Has cell scope.
		private int index;

		public SortRightCells() {
			super("Sorting Right Cells");
		}

		/**
		 * Increases the index in the renamedVars list
		 * @param newVar
		 */
		@Override
		void updateRenamedVars(Variable newVar) {
			index++;
		}

		/**
		 * Attempts to retrieve the list of renamed vars corresponding to
		 * the current framingVariable.
		 * @param node unused
		 * @return false, if no renamed vars are found, true owise/
		 */
		@Override
		boolean initializeRenamedVars(Cell node) {
			renamedVars = null;
			if (framingVariable != null) {
				final Cell cell = variables.get(framingVariable);
				if (cell == null) return false;
				renamedVars = ((Bag) cell.getContents
						()).getContents();
				index = 0;
			}
			return true;
		}

		/**
		 * Gets the replacement variable from the current index
		 * @param cellsExist unused
		 * @param multiplicity unused
		 * @return the current replacement variable, or null if none exist.
		 */
		@Override
		Variable getReplacementVariable(boolean cellsExist, Cell.Multiplicity multiplicity) {
			if (framingVariable == null) return null;
			return (Variable)renamedVars.get(index);
		}
	}

	/**
	 * Generic class for sorting the cells.
	 */
	private abstract class SortCellCells extends CopyOnWriteTransformer {
		private Map<String,List<Term>> cellMap;
		/**
		 * Variable used for framing the rest of the current cell.
		 * Scope: current cell.
		 */
		Variable framingVariable;
		/**
		 * List of variables meant to replace the framing Variable.
		 */
		List<Term> renamedVars;

		protected SortCellCells(String name) {
			super(name);
		}

		@Override
		public ASTNode transform(Cell node) throws TransformerException {
			ASTNode astNode = super.transform(node);
			if (astNode != node) {
				node = (Cell) astNode;
			}
//			System.out.println(node.getId());
			return transformTop(node);
		}

		/**
		 * Sorts the cells of a given cell node according to the configuration.
		 * @param node
		 * @return a new cell with its cells sorted.
		 */
		ASTNode transformTop(Cell node) {
			ConfigurationStructureMap config = resolveConfigurationAbstraction.cfgStr;
			ConfigurationStructure cfgStr = config.get(node.getId());
			if (cfgStr.sons.isEmpty()) {
				return node;
				// nothing to sort (not a cell holding cells,
				// e.g., the k cell, or a Map)
			}
			List<Term> cfgCells = cfgStr.cell.getCellTerms();
			initializeCellMap(node);

			Bag outBag;
			outBag = getOutputBag(cfgCells, node);
			node = node.shallowCopy();
			node.setContents(outBag);
			return node;
		}

		/**
		 * Builds a list of elements, each containing the corresponding cell
		 * (s) in the order specified by the configuration and/or a variable.
		 * @param cfgCells  the list of cells as specified by the
		 *                        configuration.
		 * @param node  the original cell holding the cells.
		 * @return  the list of sorted cells
		 */
		private Bag getOutputBag(List<Term> cfgCells, Cell node) {
			boolean foundRenamedVar = initializeRenamedVars(node);
			if (!foundRenamedVar) {
			// for rhs if variable does not come from
			// a cell in the lhs.  If so, we need to handle it as if it were
			// a lhs cell, to get the variable replacements and apply them
			// accordingly.
				Cell newCell = (Cell) new SortLeftCells().transformTop(node);
				return (Bag) newCell.getContents();
			}
			Bag outBag = new Bag();
			List<Term> outCells = outBag.getContents();
			for (Term cCell : cfgCells) {
				if (cCell instanceof TermComment) continue; //skip <br/>
				Cell cell = (Cell) cCell;
				final Cell.Multiplicity multiplicity = cell.getMultiplicity();
				Variable newVar;
				List<Term> iCells = cellMap.get(cell.getId());
				newVar = getReplacementVariable(
						iCells != null,
						multiplicity);
				if (iCells == null) { // sanity and definition checks
					if (newVar == null &&
							(multiplicity == Cell.Multiplicity.ONE	||
									multiplicity == Cell.Multiplicity.SOME)) {
						GlobalSettings.kem.register(new KException(KException
								.ExceptionType.ERROR,
								KException.KExceptionGroup.COMPILER,
								"Cell " + cell.getId() + " is missing from " +
										"cell " + node.getId(),
								getName(), node.getFilename(),
								node.getLocation()));
					}
					iCells = new ArrayList<Term>();
				} else {
					if ((iCells.size() > 1 || newVar != null) &&
							(multiplicity == Cell.Multiplicity.ONE ||
									multiplicity == Cell.Multiplicity.MAYBE)) {
						GlobalSettings.kem.register(new KException(KException
								.ExceptionType.ERROR,
								KException.KExceptionGroup.COMPILER,
								"Cell " + cell.getId() + " is found " +
										iCells.size() + " times in cell" +
										node.getId() + " but its multiplicity" +
										" is " + multiplicity,
								getName(),
								node.getFilename(), node.getLocation()));
					}
				}
				if (newVar != null) {
					iCells.add(newVar);
				}
				if (multiplicity == Cell.Multiplicity.ONE) {
					if (iCells.size() != 1) { // another sanity check
						GlobalSettings.kem.register(new KException(KException
								.ExceptionType.ERROR,
								KException.KExceptionGroup.COMPILER,
								"Cell " + cell.getId() + " is found " +
										iCells.size() + " times in cell" +
										node.getId() + " but its multiplicity" +
										" " +
										"is " + multiplicity,
								getName(),
								node.getFilename(), node.getLocation()));
					}
					// if multiplicity is one, just add an item
					outCells.add(iCells.get(0));
				} else { // else, add cells and variables as a bag.
					outCells.add(new Bag(iCells));
				}
				updateRenamedVars(newVar);
			}
			return outBag;
		}

		abstract void updateRenamedVars(Variable newVar);

		abstract boolean initializeRenamedVars(Cell node);

		abstract Variable getReplacementVariable(boolean cellsExist,
												 Cell.Multiplicity multiplicity);


		/**
		 * Populates a map containing for each cell name the list of cells
		 * with that name in the current cell.
		 *
		 * It also sets the framing variable if found in the current cell.
		 * @param node  the current cell
		 */
		private void initializeCellMap(Cell node) {
			List<Term> cells = node.getCellTerms();
			framingVariable = null;
			cellMap = new HashMap<String, List<Term>>();
			for (Term i : cells) {
				if (i instanceof Empty || i instanceof TermComment) continue;
				if (i instanceof Variable) {
					if (framingVariable !=null) { //2 vars in a cell?
						GlobalSettings.kem.register(new KException(KException
								.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
								"two variables in the same cell.", getName(),
								node.getFilename(), node.getLocation()));
					}
					framingVariable = (Variable) i;
					continue;
				}
				if (!(i instanceof Cell)) { //only cells allowed
					GlobalSettings.kem.register(new KException(KException
							.ExceptionType.ERROR,
							KException.KExceptionGroup.COMPILER,
							"unexpected item " + i + " in cell contents.",
							getName(),
							i.getFilename(), i.getLocation()));
				}
				Cell cell = (Cell) i;
				List<Term> iCells = cellMap.get(cell.getId());
				if (iCells == null) {
					iCells = new ArrayList<Term>();
					cellMap.put(cell.getId(), iCells);
				}
				iCells.add(i);
			}
		}


	}

	/**
	 * Updates cell variables which are found outside of cells (i.e.,
	 * which are either saved into or restored from a location).  For example
	 * the rules for saving the control in the call stack or exception stack.
	 */
	private class ResolveRemainingVariables extends CopyOnWriteTransformer {
		private ResolveRemainingVariables() {
			super("SortCells: resolving remaining variables");
		}

		/**
		 * Transforms remaining cell variables into cell-fragments.
		 *
		 * These variables are replaced with cell fragments wrapping the renamed
		 * variables associated to them, where a null position in a list
		 * (corresponding to a missing variable) is replaced by the empty bag.
		 *
		 * @param node  the current variable being visited
		 * @return the corresponding cell-fragment if a cell variable or the
		 * variable, owise
		 * @throws TransformerException
		 */
		@Override
		public ASTNode transform(Variable node) throws TransformerException {
			Cell cell = variables.get(node);
			if (cell == null) return  node;
			Bag bag = (Bag) cell.getContents().shallowCopy();
			List<Term> renamedVars = new ArrayList<Term>(bag.getContents());
			bag.setContents(renamedVars);
			cell = cell.shallowCopy();
			cell.setContents(bag);
			final String label = cell.getLabel() + "-fragment";
			cell.setLabel(label);
			cell.setId(label);
			for (int i = 0; i < renamedVars.size(); i++) {
				Term t = renamedVars.get(i);
				if (t == null) {
					renamedVars.set(i,new Empty(MetaK.Constants.Bag));
				}
			}
			return cell;
		}
	}
}
