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
	Map<Variable,Map<String,Term>> variables
			= new HashMap<Variable, Map<String, Term>>();
	Map<Term,Term> substitution = new HashMap<Term, Term>();

	private final ConfigurationStructureMap configurationStructureMap;


	public SortCells(ConfigurationStructureMap configurationStructureMap) {
		super("SortCells");
		this.configurationStructureMap = configurationStructureMap;
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

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		variables.clear();
		substitution.clear();
		Term body = node.getBody();
		if (!(body instanceof Rewrite)) {
			GlobalSettings.kem.register(new KException(KException
					.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
					"All rules should have rewrite at top by now", getName(),
					node.getFilename(), node.getLocation()));
		}
		Rewrite rew = (Rewrite)body.accept(this);
		if (rew == body) return node;
		node = node.shallowCopy();
		node.setBody(rew);
		return node.accept(new ResolveRemainingVariables());
	}

	private Map<String,List<Term>> cellMap;
	Map<String, Term> renamedVars;
	Variable framingVariable;

	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		ASTNode astNode = super.transform(node);
		if (astNode != node) {
			node = (Cell) astNode;
		}
//			System.out.println(node.getId());
		return transformTop(node, false);
	}

	ASTNode transformTop(Cell node, boolean fragment) {
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
		outBag = getOutputBag(cfgCells, node, fragment);
		node = node.shallowCopy();
		node.setContents(outBag);
		return node;
	}

	private Bag getOutputBag(List<Term> cfgCells, Cell node, boolean fragment) {
		initializeRenamedVars(node);
		Bag outBag = new Bag();
		List<Term> outCells = outBag.getContents();
		for (Term cCell : cfgCells) {
			if (cCell instanceof TermComment) continue;
			Cell cell = (Cell) cCell;
			final Cell.Multiplicity multiplicity = cell.getMultiplicity();
			Term replacementTerm;
			List<Term> iCells = cellMap.get(cell.getId());
			replacementTerm = getReplacementTerm(cell, fragment);
				/*
					null --- unset
			  		Variable
			    	--- Bag
			    	--- BagItem
			   		Empty(Bag)
			 	*/
			if (iCells == null) {
				if (replacementTerm instanceof Empty &&
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

			if (!(replacementTerm instanceof Empty) && replacementTerm != null) {
				iCells.add(replacementTerm);
			}
			if (multiplicity == Cell.Multiplicity.ONE) {
				if (iCells.size() != 1) {
					System.out.println(iCells.toString());
					GlobalSettings.kem.register(new KException(KException
							.ExceptionType.ERROR,
							KException.KExceptionGroup.COMPILER,
							"Cell " + cell.getId() + " is found " +
									iCells.size() + " times in cell " +
									node.getId() + " but its multiplicity " +
									"is " + multiplicity,
							getName(),
							node.getFilename(), node.getLocation()));
				}
				outCells.add(iCells.get(0));
			} else {
				outCells.add(new Bag(iCells));
			}
		}
		return outBag;
	}

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

	boolean initializeRenamedVars(Cell node) {
		if (framingVariable != null) {
			renamedVars = variables.get(framingVariable);
			if (null == renamedVars) {
				renamedVars = new HashMap<String, Term>();
				variables.put(framingVariable, renamedVars);
			}
		} else {
			renamedVars = null;
		}
		return true;
	}

	Term getReplacementTerm(Cell cell,
							boolean fragment) {
		if (framingVariable == null) return null;
		Cell.Multiplicity multiplicity = cell.getMultiplicity();
		List<Term> iCells = cellMap.get(cell.getId());
		Term replacementTerm =  new Empty(KSort.Bag.name());
		if (iCells != null) {
			if (multiplicity == Cell.Multiplicity.ANY ||
					multiplicity == Cell.Multiplicity.SOME) {
				replacementTerm = MetaK.getFreshVar(MetaK.Constants.Bag);
			}
		} else {
			if (multiplicity == Cell.Multiplicity.ONE && !fragment) {
				replacementTerm = MetaK.getFreshVar(MetaK.Constants.BagItem);
			} else {
				replacementTerm = MetaK.getFreshVar(MetaK.Constants.Bag);
			}
		}
		Term oldTerm = renamedVars.get(cell.getId());
			/*
			   null --- unset
			   Variable
			     --- Bag
			     --- BagItem
			   Empty(Bag)
			 */
		if (oldTerm == null) {
			renamedVars.put(cell.getId(),replacementTerm);
			return replacementTerm;
		}
		if (replacementTerm instanceof Empty) {
			if (oldTerm.getSort().equals(KSort.BagItem.name())) {
				GlobalSettings.kem.register(new KException(KException
						.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
						"Multiplicity constraints clash for cell" +
								cell.getId(),
						getName(), cell.getFilename(), cell.getLocation()));
			}
			if (oldTerm instanceof Variable) {
				substitution.put(oldTerm, replacementTerm);
				renamedVars.put(cell.getId(),replacementTerm);
			}
			return replacementTerm;
		}
		if (oldTerm instanceof Empty && replacementTerm.getSort().equals
				(KSort.BagItem.name())) {
			GlobalSettings.kem.register(new KException(KException
					.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
					"Multiplicity constraints clash for cell" +
							cell.getId(),
					getName(), cell.getFilename(), cell.getLocation()));
		}
		return oldTerm;
	}

	public Term getCellFragment(Variable node) {
		final Map<String, Term> cellMap = variables.get(node);
		if (cellMap == null) return node;
		Cell fragment = new Cell();
		fragment.setLabel("cell-fragment");
		Bag outBag = new Bag();
		fragment.setContents(outBag);
		for (Term value : cellMap.values()) {
			outBag.add(value);
		}
		return fragment;
	}

	private class ResolveRemainingVariables extends CopyOnWriteTransformer {
		private ResolveRemainingVariables() {
			super("SortCells: resolving remaining variables");
		}

		@Override
		public ASTNode transform(Variable node) throws TransformerException {
			if (variables.containsKey(node)) {
				GlobalSettings.kem.register(new KException(KException
						.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
						"Unresolved cell contents variable" + node + " .  " +
								"Maybe you forgot to annotate the operation " +
								"as containing a CellFragment.",
						getName(), node.getFilename(), node.getLocation()));
			}
			Term repl = substitution.get(node);
			if (repl != null) return repl;
			return node;
		}
	}
}
