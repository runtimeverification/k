package org.kframework.compile.transformers;

import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Collection;
import org.kframework.kil.Context;
import org.kframework.kil.loader.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.*;
import java.util.List;
import java.util.Map;
import java.util.Set;

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


	public SortCells(org.kframework.kil.loader.Context context) {
		super("SortCells", context);
		this.configurationStructureMap = context.getConfigurationStructureMap();
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
//        System.out.println(node.getLocation());
//        node = checkCollapsingCellRule(node);
        boolean change = false;
		variables.clear();
		substitution.clear();
		Term body = node.getBody();
		ASTNode bodyNode = body.accept(this);
        if (bodyNode != body) change = true;
        Term requires = node.getRequires();
        Term requiresNode = null;
        if (requires != null) {
           requiresNode = (Term) requires.accept(this);
           if (requiresNode != requires) change = true;
        }
        //TODO:  Handle ensures?
        if (!change) return node;
		node = node.shallowCopy();
		node.setBody((Term) bodyNode);
        node.setRequires(requiresNode);
		return node.accept(new ResolveRemainingVariables(context));
	}

//    private Rule checkCollapsingCellRule(Rule node) {
//        assert node.getBody() instanceof Rewrite;
//        Rewrite rew = (Rewrite) node.getBody();
//        if (rew.getLeft() instanceof Cell) {
//            Term right = rew.getRight();
//            if (right instanceof Cell) return node;
//            if (right instanceof Bag) {
//                assert ((Bag) right).getContents().isEmpty();
//            } else {
//                assert right instanceof Empty;
//            }
//            right = new Empty(MetaK.cellFragment(((Cell) rew.getLeft()).getId()));
//            rew = rew.shallowCopy();
//            rew.setRight(right);
//            node = node.shallowCopy();
//            node.setBody(rew);
//        }
//        return node;
//    }

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

	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		ASTNode astNode = super.transform(node);
		if (astNode != node) {
			node = (TermCons) astNode;
		}
		Production production = node.getProduction();
		Map<Integer, String> cellsorts = getCellSorts(production);
		int i;
		if (cellsorts.isEmpty()) return node;
		TermCons outNode = node.shallowCopy();
		final ArrayList<Term> outList = new ArrayList<Term>();
		outNode.setContents(outList);
		i = 0;
		for (Term t : node.getContents()) {
			Term out = t;
			String sort = cellsorts.get(new Integer(i));
			if (sort != null) {
				assert (KSort.valueOf(t.getSort())
						.mainSort().equals(KSort.Bag));
				if (MetaK.isCellFragment(sort)) {
					Cell fragment = new Cell();
					fragment.setLabel(context.getCellSort(sort));
//					System.err.println(fragment.getLabel());
					fragment.setContents(t);
					fragment = (Cell) transformTop(fragment, true);
					out = fragment;
				} else {
					out = out.shallowCopy();
					out.setSort(sort);
				}
			}
			outList.add(out);
			i++;
		}
		return outNode;
	}

	private Map<Integer, String> getCellSorts(Production production) {
		Map<Integer, String> cellsorts = new HashMap<Integer, String>();
		int i = 0;
		for (ProductionItem pitem : production.getItems()) {
			if (pitem instanceof Sort) {
				final Sort sort = (Sort) pitem;
				final String realName = sort.getRealName();
				final Integer key = new Integer(i);
				String oldsort = cellsorts.get(key);
				if (MetaK.isCellSort(realName)) {
					assert (oldsort == null || oldsort.equals(realName)) ;
					cellsorts.put(key, realName);
				} else assert  (oldsort == null) ;
				i++;
			}
		}
		return cellsorts;
	}

	@Override
	public ASTNode transform(KApp node) throws TransformerException {
		ASTNode astNode = super.transform(node);
		if (astNode != node) {
			node = (KApp) astNode;
		}
		Term klabel = node.getLabel();
		if (!(klabel instanceof KLabelConstant)) return node;
		KLabelConstant label = (KLabelConstant) klabel;
		Set<Production> productions =
				context.productions.get(
						StringUtil.unescapeMaude(label.getLabel()));
		if (productions == null|| productions.isEmpty())
			return node;
		Map<Integer, String> cellfragments = new HashMap<Integer, String>();
		for (Production prod : productions) {
			int i = 0;
			for (ProductionItem pitem : prod.getItems()) {
				if (pitem instanceof Sort) {
					final Sort sort = (Sort) pitem;
					final String realName = sort.getRealName();
					final Integer key = new Integer(i);
					String oldsort = cellfragments.get(key);
					if (MetaK.isCellSort(realName)) {
						assert (oldsort == null || oldsort.equals(realName));
						cellfragments.put(key, realName);
					} else assert (oldsort == null);
					i++;
				}
			}
		}
		if (cellfragments.isEmpty()) return node;
        KApp oldNode = node;
		node = node.shallowCopy();
		Term child = node.getChild();
		if (!(child instanceof KList)) {
			KList newChild = new KList();
			if (!(child instanceof Empty))
				newChild.add(child);
			child = newChild;
		}
		KList kList = (KList) child;
		KList outkList = kList.shallowCopy();
		node.setChild(outkList);
		final ArrayList<Term> outList = new ArrayList<Term>();
		outkList.setContents(outList);
		int i = 0;
		for (Term t : kList.getContents()) {
            if (t.getSort().equals(KSort.KList.name())) return oldNode;
			String sort = cellfragments.get(new Integer(i));
			if (sort != null) {
				assert (t instanceof KApp);
				t = t.shallowCopy();
				KApp kApp = (KApp) t;
				if (kApp.getChild() instanceof KList) {
					assert((KList) kApp
						.getChild()).getContents().isEmpty();
				} else assert  ((kApp.getChild() instanceof Empty));
				final Term kAppLabel = kApp.getLabel().shallowCopy();
				assert ((kAppLabel instanceof KInjectedLabel));
				kApp.setLabel(kAppLabel);

				final KInjectedLabel kInjectedLabel = (KInjectedLabel) kAppLabel;
				Term bag = kInjectedLabel.getTerm();
				assert  bag.getSort().equals("Bag")
						||	bag.getSort().equals("BagItem")
						|| MetaK.isCellSort(bag.getSort());
				if (MetaK.isCellFragment(sort)) {
					Cell fragment = new Cell();
					fragment.setLabel(context.getCellSort(sort));
					fragment.setContents(bag);
					fragment = (Cell) transformTop(fragment, true);
					kInjectedLabel.setTerm(fragment);
				} else {
					bag = bag.shallowCopy();
					bag.setSort(sort);
					kInjectedLabel.setTerm(bag);
				}
			}
			outList.add(t);
			i++;
		}
		return node;
	}

	ASTNode transformTop(Cell node, boolean fragment) {
		ConfigurationStructureMap config = configurationStructureMap;
		String id = node.getId();
        node = node.shallowCopy();
		if (fragment) {
//            System.out.println(node);
			id = id.substring(0, id.length()-"-fragment".length());
            node.setSort(MetaK.cellFragment(id));
		} else {
            node.setSort(MetaK.cellSort(id));
        }
		ConfigurationStructure cfgStr = config.get(id);
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
				if (!fragment && replacementTerm instanceof Empty &&
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
			if (iCells.isEmpty()) {
                outCells.add(new Empty(MetaK.cellFragment(cell.getId())));
			} else {
				if (multiplicity == Cell.Multiplicity.ONE) {
					if (iCells.size() != 1) {
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
		Term replacementTerm =  new Empty(MetaK.cellFragment(cell.getId()));
		if (iCells != null) {
			if (multiplicity == Cell.Multiplicity.ANY ||
					multiplicity == Cell.Multiplicity.SOME) {
				replacementTerm = Variable.getFreshVar(MetaK.cellFragment(cell.getId()));
			}
		} else {
			if (multiplicity == Cell.Multiplicity.ONE && !fragment) {
				replacementTerm = Variable.getFreshVar(MetaK.cellSort(cell.getId()));
			} else {
				replacementTerm = Variable.getFreshVar(MetaK.cellFragment(cell.getId()));
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
			if (oldTerm.getSort().equals(MetaK.cellSort(cell.getId()))) {
				GlobalSettings.kem.register(new KException(KException
						.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
						"Multiplicity constraints clash for cell " +
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
				(MetaK.cellSort(cell.getId()))) {
			GlobalSettings.kem.register(new KException(KException
					.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
					"Multiplicity constraints clash for cell " +
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
		private ResolveRemainingVariables(org.kframework.kil.loader.Context context) {
			super("SortCells: resolving remaining variables", context);
		}

		@Override
		public ASTNode transform(Variable node) throws TransformerException {
			if (variables.containsKey(node)) {
				GlobalSettings.kem.register(new KException(KException
						.ExceptionType.ERROR, KException.KExceptionGroup.COMPILER,
						"Unresolved cell contents variable " + node + " .  " +
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
