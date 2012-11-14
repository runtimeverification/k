package org.kframework.compile.utils;

import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Collection;
import org.kframework.kil.Map;
import org.kframework.kil.ProductionItem.ProductionType;
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

import java.util.*;
import java.util.List;
import java.util.Set;

public class MetaK {

   public static class Constants {

        public static final String anyVarSymbol = "_";
        public static final String heatingTag = "heating";
        public static final String KItem = "KItem";
        public static final String K = "K";
        public static final String hole = "[]";
   }

	static int nextVarId = 0;

    public static Set<String> kModules = new HashSet<String>();
	static {
		kModules.add("K-BUILTINS");
		kModules.add("K-CONDITION-SEARCH");
		kModules.add("K-CONFIG");
		kModules.add("K-CONTEXTS");
		kModules.add("K-LATEX");
		kModules.add("K-OPEN-CELLS");
		kModules.add("K-POLYMORPHIC-VARIABLES");
		kModules.add("K-PROPER");
		kModules.add("K-QUOTED-LABELS");
		kModules.add("K-RESULT");
		kModules.add("K-RULES");
		kModules.add("K-SENTENCE");
		kModules.add("K-STRICNESS");
		kModules.add("K-TECHNIQUE");
		kModules.add("K-WHERE");
		kModules.add("K-WRAPPERS");
		kModules.add("K-WRAPPERS-LABELS");
	};

	public static Set<String> builtinSorts = new HashSet<String>();
	static {
		builtinSorts.add("Bool");
		builtinSorts.add("Float");
		builtinSorts.add("Id");
		builtinSorts.add("Int");
		builtinSorts.add("String");
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
		return new Empty("K");
	}

	public static Term kWrapper(Term t) {
		if (DefinitionHelper.isSubsortedEq("K", t.getSort()))
			return t;
		return new KApp(new KInjectedLabel(t), new ListOfK());
	}

	public static boolean isKSort(String sort) {
		try {
			KSort.valueOf(sort);
		} catch (IllegalArgumentException e) {
			return sort.equals("List{K}");
		}
		return true;
	}

	public static boolean isAnywhere(Rule r) {
		Attributes attrs = r.getAttributes();
		if (null == attrs)
			return false;
		for (Attribute any : anywheres) {
			if (any.getValue() == attrs.get(any.getKey()))
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
			public void visit(ListOfK node) {
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
		if (prod.isSubsort())
			return getFreshVar(prod.getItems().get(0).toString());
		if (prod.isConstant())
			return new Constant(prod.getSort(), ((Terminal) prod.getItems().get(0)).getTerminal());
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
		}
		return null;
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
 }
