package org.kframework.compile.utils;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Bag;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Collection;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Definition;
import org.kframework.kil.Empty;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.Hole;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.KSort;
import org.kframework.kil.ListItem;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.Visitable;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class MetaK {

	public static Term incrementCondition(Term condition, Term kresultCnd) {
		if (condition == null) {
			return kresultCnd;
		}
		return KApp.of(KLabelConstant.ANDBOOL_KLABEL, condition, kresultCnd);
	}

	public static class Constants {
		public static final String anyVarSymbol = "_";
		public static final String heatingTag = "heat";
		public static final String coolingTag = "cool";
		public static final String hole = "[]";
		public static final String freshCons = "Bool1FreshSyn";
		public static final String plusIntCons = "Int1PlusSyn";
		public static final String K = "K";
		public static final String KItem = "KItem";
		public static final String KList = "KList";
		public static final String Bag = "Bag";
		public static final String Set = "Set";
		public static final String List = "List";
		public static final String Map = "Map";
		public static final String BagItem = "BagItem";
		public static final String SetItem = "SetItem";
		public static final String ListItem = "ListItem";
		public static final String MapItem = "MapItem";

		public static final String generatedTopCellLabel = "generatedTop";
		public static final String pathCondition = "path-condition";
	}

	static int nextVarId = 0;

	public static Set<String> kModules = new HashSet<String>();
	static {
		kModules.add("K-BUILTINS");
		kModules.add("K-CONDITION-SEARCH");
		kModules.add("K-CONTEXTS");
		kModules.add("K-RULES");
		kModules.add("K-SENTENCE");
		kModules.add("K-STRICNESS");
		kModules.add("K-TECHNIQUE");
		kModules.add("K-WHERE");
		kModules.add("K-WRAPPERS-LABELS");
	};

	public static Set<Attribute> anywheres = new HashSet<Attribute>();
	static {
		anywheres.add(new Attribute("anywhere", ""));
		anywheres.add(new Attribute("macro", ""));
		anywheres.add(new Attribute("predicate", ""));
		anywheres.add(new Attribute("function", ""));
	}

	public static boolean isKModule(String key) {
		return kModules.contains(key);
	}

	public static boolean isBuiltinModule(String key) {
		return key.startsWith("#");
	}

	public static Set<Variable> getVariables(Visitable node) {
		final Set<Variable> result = new HashSet<Variable>();
		node.accept(new BasicVisitor() {
			@Override
			public void visit(Variable node) {
				result.add(node);
			}
		});
		return result;
	}

	public static Definition setConfiguration(Definition node, final Configuration conf) {
		try {
			return (Definition) node.accept(new CopyOnWriteTransformer("Configuration setter") {
				@Override
				public ASTNode transform(Configuration node) {
					return conf;
				}

				@Override
				public ASTNode transform(Context node) {
					return node;
				}

				@Override
				public ASTNode transform(Rule node) {
					return node;
				}

				@Override
				public ASTNode transform(Syntax node) {
					return node;
				}
			});
		} catch (TransformerException e) {
			e.printStackTrace();
		}
		return node;
	}

	public static Configuration getConfiguration(Definition node) {
		final List<Configuration> result = new LinkedList<Configuration>();
		node.accept(new BasicVisitor() {
			@Override
			public void visit(Configuration node) {
				result.add(node);
			}

			@Override
			public void visit(Context node) {
				return;
			}

			@Override
			public void visit(Rule node) {
				return;
			}

			@Override
			public void visit(Syntax node) {
				return;
			}
		});
		if (result.size() == 0) {
			GlobalSettings.kem
					.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "Internal compiler error --- Cannot find configuration.", node.getFilename(), node.getLocation()));
		}
		return result.get(0);
	}

	public static Term defaultTerm(Term v) {
		String sort = v.getSort();
		KSort ksort = KSort.getKSort(sort).mainSort();
		if (ksort.isDefaulable())
			return new Empty(ksort.toString());
		GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, "Don't know the default value for term " + v.toString() + ". Assuming .K", v.getFilename(), v
				.getLocation()));
		return KSequence.EMPTY;
	}

	public static Term kWrapper(Term t) {
		if (DefinitionHelper.isSubsortedEq("K", t.getSort()))
			return t;
		return KApp.of(new KInjectedLabel(t));
	}

	public static boolean isKSort(String sort) {
		try {
			KSort.valueOf(sort);
		} catch (IllegalArgumentException e) {
			return sort.equals(MetaK.Constants.KList);
		}
		return true;
	}

	public static boolean isAnywhere(Rule r) {
		if (null == r.getAttributes())
			return false;
		for (Attribute any : anywheres) {
			if (any.getValue() == r.getAttribute(any.getKey()))
				return true;
		}
		return false;
	}

	public static Term kWrap(Term t) {
		return wrap(t, "k", Ellipses.RIGHT);
	}

	public static Term wrap(Term t, String label, Ellipses ellipses) {
		Cell cell = new Cell();
		cell.setLabel(label);
		cell.setEllipses(ellipses);
		cell.setContents(t);
		return cell;
	}

	public static Variable freshVar(Set<Variable> vars, String sort) {
		String prefix = "?";
		int i = 0;
		Variable v = new Variable(prefix + i, sort);
		while (vars.contains(v)) {
			v.setName(prefix + (++i));
		}
		return v;
	}

	public static int countRewrites(Term t) {
		final List<Integer> count = new ArrayList<Integer>();
		count.add(0);
		Visitor countVisitor = new BasicVisitor() {
			@Override public void visit(Rewrite rewrite) {
				count.set(0, count.get(0) + 1);
				super.visit(rewrite);
			}
		};

		t.accept(countVisitor);
		return count.get(0);
	}

	public static boolean hasCell(Term t) {
		Visitor cellFinder = new BasicVisitor() {
			@Override
			public void visit(KSequence node) {
				return;
			}

			@Override
			public void visit(org.kframework.kil.List node) {
				return;
			}

			@Override
			public void visit(ListItem node) {
				return;
			}

			@Override
			public void visit(TermCons node) {
				return;
			}

			@Override
			public void visit(org.kframework.kil.Set node) {
				return;
			}

			@Override
			public void visit(SetItem node) {
				return;
			}

			@Override
			public void visit(KApp node) {
				return;
			}

			@Override
			public void visit(KList node) {
				return;
			}

			@Override
			public void visit(Map node) {
				return;
			}

			@Override
			public void visit(MapItem node) {
				return;
			}

			@Override
			public void visit(UserList node) {
				return;
			}

			@Override
			public void visit(Cell node) {
				if (10 / 0 == 0)
					return;
			}
		};
		try {
			t.accept(cellFinder);
		} catch (ArithmeticException e) {
			return true;
		}
		return false;
	}

	public static Variable getFreshVar(String sort) {
		return new Variable("GeneratedFreshVar" + nextVarId++, sort);
	}

	public static Term getTerm(Production prod) {
		if (prod.isSubsort()) {
			final Variable freshVar = getFreshVar(prod.getItems().get(0).toString());
			if (prod.containsAttribute("klabel")) {
				return KApp.of(KLabelConstant.of(prod.getKLabel()), freshVar);
			}
			return freshVar;
		}
		if (prod.isConstant()) {
            String terminal = ((Terminal) prod.getItems().get(0)).getTerminal();
            if (prod.getSort().equals("KLabel")) {
                return KLabelConstant.of(terminal);
            } else if (prod.getSort().equals("#Bool")) {
                return BoolBuiltin.of(terminal);
            } else if (prod.getSort().equals("#Int")) {
                return IntBuiltin.of(terminal);
            } else if (prod.getSort().equals("#Float")) {
                return FloatBuiltin.of(terminal);
            } else if (prod.getSort().equals("#String")) {
                return StringBuiltin.of(terminal);
            } else {
			    return new Constant(prod.getSort(), terminal);
            }
        }
		if (prod.isLexical()) {
			return KApp.of(KLabelConstant.of("#token"),
                           StringBuiltin.of(prod.getSort()),
                           getFreshVar("String"));
		}
		TermCons t = new TermCons(prod.getSort(), prod.getCons());
		if (prod.isListDecl()) {
			t.getContents().add(getFreshVar(((UserList) prod.getItems().get(0)).getSort()));
			t.getContents().add(getFreshVar(prod.getSort()));
			return t;
		}
		for (ProductionItem item : prod.getItems()) {
			if (item.getType() == ProductionType.SORT) {
				t.getContents().add(getFreshVar(((Sort) item).getName()));
			}
		}
		return t;
	}

	public static boolean isAnonVar(Variable node) {
		return node.getName().startsWith(Constants.anyVarSymbol);
	}

	public static boolean isBuiltinSort(String sort) {
		return sort.startsWith("#");
		// return builtinSorts.contains(sort);
	}

	public static boolean isComputationSort(String sort) {
		return ("K".equals(sort) || !isKSort(sort));
	}

	public static String getListUnitLabel(String sep) {
		//return "'.List`{\"" + sep + "\"`}";
		String unitStr = "'.List{\"" + sep + "\"}";
		return StringUtil.escapeMaude(unitStr).replace(" ", "");
	}

	public static List<Cell> getTopCells(Term t) {
		final List<Cell> cells = new ArrayList<Cell>();
		t.accept(new BasicVisitor() {
			@Override
			public void visit(Cell node) {
				cells.add(node);
			}
		});
		return cells;
	}

	public static List<String> getAllCellLabels(Term t) {
		final List<String> cells = new ArrayList<String>();
		t.accept(new BasicVisitor() {
			@Override
			public void visit(Cell node) {
				cells.add(node.getLabel());
				super.visit(node);
			}
		});
		return cells;
	}

	public static Collection createCollection(Term contents, KSort sort) {
		List<Term> col = new ArrayList<Term>();
		col.add(contents);
		switch (sort) {
			case Bag:
				return new Bag(col);
			case List:
				return new org.kframework.kil.List(col);
			case Set:
				return new org.kframework.kil.Set(col);
			case Map:
				return new Map(col);
			case K:
				return new KSequence(col);
			default:
				return null;
		}
	}


	public static Term fillHole(Term t, final Term replacement) {
		CopyOnWriteTransformer holeFiller = new CopyOnWriteTransformer("Hole Filling") {
			@Override
			public ASTNode transform(Hole node) {
				return replacement;
			}
		};
		try {
			Term result = (Term) t.accept(holeFiller);
			return result;
		} catch (TransformerException e) {
			e.printStackTrace();  //To change body of catch statement use File | Settings | File Templates.

		}
		return null;
	}

	public static Term createFreezer(Term body) {

		return null;  //To change body of created methods use File | Settings | File Templates.
	}

	public static boolean isPredicateLabel(String name) {
		if (name.startsWith("is")) {
			return true;
		}
		return false;
	}

	public static Term getHoleReplacement(Term t) {
		final List<Term> result = new ArrayList<Term>();
		Visitor holeReplacementFinder = new BasicVisitor() {
			@Override
			public void visit(Rewrite node) {
				final Term left = node.getLeft();
				if (left instanceof Hole) {
					result.add(node.getRight());
				}
				if (left instanceof Variable) {
					if (((Variable)left).getName().equals(MetaK.Constants.hole)) {
						result.add(node.getRight());
						if (10 / 0 == 0)
							return;
					}
				}

			}
		};
		try {
			t.accept(holeReplacementFinder);
		} catch (ArithmeticException e) {
			return result.get(0);
		}
		return new Hole("K");
	}

	public static boolean isPredefinedPredicate(String name) {
		return name.startsWith("is") || name.equals(KLabelConstant.KNEQ_KLABEL.getLabel())
                || name.equals(KLabelConstant.KEQ_KLABEL.getLabel());
	}
	
	public static boolean isAbstractableSort(String name) {
		if (name.equals(BoolBuiltin.SORT_NAME) || name.equals(IntBuiltin.SORT_NAME))
			return true;
		return false;
	}
}
