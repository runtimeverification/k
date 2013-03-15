package org.kframework.compile.transformers;

import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Collection;
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
 * Prerequisites:  Assuming that rewrites have been already pushed to the top.
 */
public class SortCells extends CopyOnWriteTransformer {

	private Map<Variable,Cell> variables
			= new HashMap<Variable, Cell>();
	private final ConfigurationStructureMap configurationStructureMap;


	public SortCells(ConfigurationStructureMap configurationStructureMap) {
		super("SortCells");
		this.configurationStructureMap = configurationStructureMap;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
//		variables.clear();
//		final Term body1 = node.getBody();
////		System.out.println(body1);
//		Term body = (Term) body1.accept(new SortRightCells());
////		System.out.println(body);
//		node = node.shallowCopy();
//		node.setBody(body);
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

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		variables.clear();
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

	private class SortLeftCells extends SortCellCells {
		public SortLeftCells() {
			super("Sorting Left Cells");
		}

		@Override
		void updateRenamedVars(Variable newVar) {
			if (framingVariable != null) {
				renamedVars.add(newVar);
			}
		}

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

	private class SortRightCells extends SortCellCells {
		private int index;

		public SortRightCells() {
			super("Sorting Right Cells");
		}

		@Override
		void updateRenamedVars(Variable newVar) {
			index++;
		}

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

		@Override
		Variable getReplacementVariable(boolean cellsExist, Cell.Multiplicity multiplicity) {
			if (framingVariable == null) return null;
			return (Variable)renamedVars.get(index);
		}
	}

	private abstract class SortCellCells extends CopyOnWriteTransformer {
		private Map<String,List<Term>> cellMap;
		Variable framingVariable;
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

		ASTNode transformTop(Cell node) {
			ConfigurationStructureMap config = configurationStructureMap;
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

		private Bag getOutputBag(List<Term> cfgCells, Cell node) {
			boolean foundRenamedVar = initializeRenamedVars(node);
			if (!foundRenamedVar) {
				Cell newCell = (Cell) new SortLeftCells().transformTop(node);
				return (Bag) newCell.getContents();
			}
			Bag outBag = new Bag();
			List<Term> outCells = outBag.getContents();
			for (Term cCell : cfgCells) {
				if (cCell instanceof TermComment) continue;
				Cell cell = (Cell) cCell;
				final Cell.Multiplicity multiplicity = cell.getMultiplicity();
				Variable newVar;
				List<Term> iCells = cellMap.get(cell.getId());
				newVar = getReplacementVariable(
						iCells != null,
						multiplicity);
				if (iCells == null) {
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
				}
//				else {
//					if ((iCells.size() > 1 || newVar != null) &&
//							(multiplicity == Cell.Multiplicity.ONE ||
//									multiplicity == Cell.Multiplicity.MAYBE)) {
//						GlobalSettings.kem.register(new KException(KException
//								.ExceptionType.ERROR,
//								KException.KExceptionGroup.COMPILER,
//								"Cell " + cell.getId() + " is found " +
//										iCells.size() + " times in cell" +
//										node.getId() + " but its multiplicity" +
//										" is " + multiplicity,
//								getName(),
//								node.getFilename(), node.getLocation()));
//					}
//				}
				if (newVar != null) {
					iCells.add(newVar);
				}
				if (multiplicity == Cell.Multiplicity.ONE) {
					if (iCells.size() != 1) {
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
					outCells.add(iCells.get(0));
				} else {
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


		private void initializeCellMap(Cell node) {
			ArrayDeque<Term> cells = new ArrayDeque<Term>(node.getCellTerms());
			framingVariable = null;
			cellMap = new HashMap<String, List<Term>>();
			while (!cells.isEmpty()) {
				Term i = cells.removeFirst();
				if (i instanceof Empty || i instanceof TermComment) continue;
				if (i instanceof Variable) {
					if (framingVariable !=null) {
						GlobalSettings.kem.register(new KException(KException
								.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
								"two variables in the same cell.", getName(),
								node.getFilename(), node.getLocation()));
					}
					framingVariable = (Variable) i;
					continue;
				}
				if (i instanceof Collection) {
					cells.addAll(((Collection)i).getContents());
					continue;
				}
				if (!(i instanceof Cell)) {
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

	private class ResolveRemainingVariables extends CopyOnWriteTransformer {
		private ResolveRemainingVariables() {
			super("SortCells: resolving remaining variables");
		}

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
