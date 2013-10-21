package org.kframework.compile.utils;

import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Collection;
import org.kframework.kil.Map;
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

import java.util.*;
import java.util.List;
import java.util.Set;

public class MetaK {

	public static final String cellSort = "CellSort";
	public static final String cellFragment = "CellFragment";

	public static Term incrementCondition(Term condition, Term kresultCnd) {
		if (condition == null) {
			return kresultCnd;
		}
		return KApp.of(KLabelConstant.ANDBOOL_KLABEL, condition, kresultCnd);
	}

	public static boolean isCellSort(String bigSort) {
		return (bigSort.endsWith(cellSort)
				||bigSort.endsWith(cellFragment));
	}

	public static boolean isCellFragment(String bigSort) {
		return (bigSort.endsWith(cellFragment));
	}

    public static String cellSort(String cellName) {
        return StringUtil.makeProper(cellName) + cellSort;
    }

    public static String cellFragment(String cellName) {
        return StringUtil.makeProper(cellName) + cellFragment;
    }

    public static String cellUnit(String cellName) {
        return "." + cellFragment(cellName);
    }

	public static class Constants {
		public static final String anyVarSymbol = "_";
		public static final String heatingTag = "heat";
		public static final String coolingTag = "cool";
		public static final String hole = "[]";
		public static final String freshCons = "Bool1FreshSyn";
		public static final String plusIntCons = "Int1PlusSyn";
        public static final String generatedTopCellLabel = "generatedTop";
		public static final String pathCondition = "path-condition";
		public static final String generatedCfgAbsTopCellLabel =
				"___CONTEXT_ABSTRACTION_TOP_CELL___";
	}

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

	public static Definition setConfiguration(Definition node, org.kframework.kil.loader.Context context, final Configuration conf) {
		try {
			return (Definition) node.accept(new CopyOnWriteTransformer("Configuration setter",
                    context) {
				@Override
				public ASTNode transform(Configuration node) {
					return conf;
				}

				@Override
				public ASTNode transform(org.kframework.kil.Context node) {
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

	public static Configuration getConfiguration(Definition node, org.kframework.kil.loader.Context context) {
		final List<Configuration> result = new LinkedList<Configuration>();
		node.accept(new BasicVisitor(context) {
			@Override
			public void visit(Configuration node) {
				result.add(node);
			}

			@Override
			public void visit(org.kframework.kil.Context node) {
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

	public static Term defaultTerm(Term v, org.kframework.kil.loader.Context context) {
		String sort = v.getSort();
		KSort ksort = KSort.getKSort(sort).mainSort();
		if (ksort.isDefaultable())
			return new Empty(ksort.toString());
		GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, "Don't know the default value for term " + v.toString() + ". Assuming .K", v.getFilename(), v
				.getLocation()));
		return KSequence.EMPTY;
	}

	public static boolean isKSort(String sort) {
		try {
			KSort.valueOf(sort);
		} catch (IllegalArgumentException e) {
			return sort.equals(KSorts.KLIST);
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

	public static Term kWrap(Term t, String komputationCellName) {
		return wrap(t, komputationCellName, Ellipses.RIGHT);
	}

	public static Term wrap(Term t, String label, Ellipses ellipses) {
		Cell cell = new Cell(t.getLocation(),t.getFilename());
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

	public static int countRewrites(Term t, org.kframework.kil.loader.Context context) {
		final List<Integer> count = new ArrayList<Integer>();
		count.add(0);
		Visitor countVisitor = new BasicVisitor(context) {
			@Override public void visit(Rewrite rewrite) {
				count.set(0, count.get(0) + 1);
				super.visit(rewrite);
			}
		};

		t.accept(countVisitor);
		return count.get(0);
	}

	public static int countHoles(Term t, org.kframework.kil.loader.Context context) {
		final List<Integer> count = new ArrayList<Integer>();
		count.add(0);
		Visitor countVisitor = new BasicVisitor(context) {
			@Override public void visit(Hole hole) {
				count.set(0, count.get(0) + 1);
				super.visit(hole);
			}
		};

		t.accept(countVisitor);
		return count.get(0);
	}

	public static boolean hasCell(Term t, org.kframework.kil.loader.Context context) {
		Visitor cellFinder = new BasicVisitor(context) {
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

    public static Term getTerm(Production prod, org.kframework.kil.loader.Context context) {
		if (prod.isSubsort()) {
			final Variable freshVar = Variable.getFreshVar(prod.getItems().get(0).toString());
			if (prod.containsAttribute("klabel")) {
				return KApp.of(KLabelConstant.of(prod.getKLabel(), context), freshVar);
			}
			return freshVar;
		}
		if (prod.isConstant()) {
            String terminal = ((Terminal) prod.getItems().get(0)).getTerminal();
            if (prod.getSort().equals(KSorts.KLABEL)) {
                return KLabelConstant.of(terminal, context);
            } else if (prod.getSort().equals(BoolBuiltin.SORT_NAME)) {
                return BoolBuiltin.kAppOf(terminal);
            } else if (prod.getSort().equals(IntBuiltin.SORT_NAME)) {
                return IntBuiltin.kAppOf(terminal);
            } else if (prod.getSort().equals(StringBuiltin.SORT_NAME)) {
                return StringBuiltin.kAppOf(terminal);
            } else {
			    return GenericToken.kAppOf(prod.getSort(), terminal);
            }
        }
		if (prod.isLexical()) {
			return KApp.of(KLabelConstant.of("#token", context),
                           StringBuiltin.kAppOf(prod.getSort()),
                           Variable.getFreshVar("String"));
		}
		TermCons t = new TermCons(prod.getSort(), prod.getCons(), context);
		if (prod.isListDecl()) {
			t.getContents().add(Variable.getFreshVar(((UserList) prod.getItems().get(0)).getSort()));
			t.getContents().add(Variable.getFreshVar(prod.getSort()));
			return t;
		}
		for (ProductionItem item : prod.getItems()) {
			if (item instanceof Sort) {
				t.getContents().add(Variable.getFreshVar(((Sort) item).getName()));
			}
		}
		return t;
	}

	public static boolean isAnonVar(Variable node) {
		return node.getName().startsWith(Constants.anyVarSymbol);
	}

	public static boolean isBuiltinSort(String sort) {
        /* TODO: replace with a proper table of builtins */
		return sort.equals(BoolBuiltin.SORT_NAME)
               || sort.equals(IntBuiltin.SORT_NAME)
               || sort.equals(StringBuiltin.SORT_NAME)
               || sort.equals("#Float")
               /* LTL builtin sorts */
//               || sort.equals("#LtlFormula")
               || sort.equals("#Prop")
               || sort.equals("#ModelCheckerState")
               || sort.equals("#ModelCheckResult");
	}

	public static boolean isComputationSort(String sort) {
		return sort.equals(KSorts.K) || sort.equals(KSorts.KITEM) || !MetaK.isKSort(sort);
	}

	public static String getListUnitLabel(String sep) {
	    return  "'.List{\"" + sep + "\"}";
    }

	public static List<Cell> getTopCells(Term t, org.kframework.kil.loader.Context context) {
		final List<Cell> cells = new ArrayList<Cell>();
		t.accept(new BasicVisitor(context) {
			@Override
			public void visit(Cell node) {
				cells.add(node);
			}
		});
		return cells;
	}

	public static List<String> getAllCellLabels(Term t, org.kframework.kil.loader.Context context) {
		final List<String> cells = new ArrayList<String>();
		t.accept(new BasicVisitor(context) {
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


	public static Term fillHole(Term t, final Term replacement, org.kframework.kil.loader.Context context) {
		CopyOnWriteTransformer holeFiller = new CopyOnWriteTransformer("Hole Filling", context) {
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

	public static Term getHoleReplacement(Term t, org.kframework.kil.loader.Context context) {
		final List<Term> result = new ArrayList<Term>();
		Visitor holeReplacementFinder = new BasicVisitor(context) {
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
		//return new Hole("K");
        return Hole.KITEM_HOLE;
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
