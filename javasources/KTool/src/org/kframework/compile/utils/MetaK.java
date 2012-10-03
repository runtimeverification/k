package org.kframework.compile.utils;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Definition;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListItem;
import org.kframework.kil.ListOfK;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rule;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.Visitable;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;


public class MetaK {
	static int nextVarId = 0;

	static String anyVarSymbol = "_";

//	public static String nextIdModules[] = {
//		"SUBSTITUTION",
//	};

	public static String kModules[] = {
		"K-CONDITION-SEARCH", 
		"K-CONFIG",
		"K-CONTEXTS", 
		"K-LATEX",
		"K-OPEN-CELLS",
		"K-POLYMORPHIC-VARIABLES",  
		"K-PROPER", 
		"K-QUOTED-LABELS",
		"K-RESULT",
		"K-RULES", 
		"K-SENTENCE", 
		"K-STRICNESS",
		"K-TECHNIQUE",
		"K-WHERE",  
		"K-WRAPPERS", 
		"K-WRAPPERS-LABELS", 
	};
	
	public static String defaultableSorts[] = {
		"Bag",
		"K",
		"List",
		"Map",
		"Set",
	};

	public static String kSorts[] = {
		"Bag",
		"BagItem",
		"CellLabel",
		"K",
		"KLabel",
		"List",
		"List{K}",
		"ListItem",
		"Map",
		"MapItem",
		"Set",
		"SetItem",
	};
	
	public static String builtinSorts[] = {
		"Bool",
		"Float",
		"Id",
		"Int",
		"String",
	};
	
	public static java.util.Map<String,String> mainSort = new HashMap<String, String>();
	static {
		mainSort.put("Bag", "Bag");
		mainSort.put("BagItem", "Bag");
		mainSort.put("Map", "Map");
		mainSort.put("MapItem", "Map");
		mainSort.put("Set", "Set");
		mainSort.put("SetItem", "Set");
		mainSort.put("List", "List");
		mainSort.put("ListItem", "List");
		mainSort.put("K", "List{K}");
		mainSort.put("List{K}", "List{K}");
	}
	
	public static Set<Attribute> anywheres = new HashSet<Attribute>();
	static {
		anywheres.add(new Attribute("anywhere", ""));
	}
	
	private static java.util.Map<String,String> maudeCollectionConstructors = new HashMap<String, String>();
	static {
		maudeCollectionConstructors.put("Bag", "__");
		maudeCollectionConstructors.put("Map", "__");
		maudeCollectionConstructors.put("Set", "__");
		maudeCollectionConstructors.put("List", "__");
		maudeCollectionConstructors.put("K", "_~>_");
		maudeCollectionConstructors.put("List{K}", "_`,`,_");
	}

	public static boolean isKModule(String key) {
		return (Arrays.binarySearch(kModules, key) >= 0);		
	}

//	public static boolean isNextIdModule(String key) {
//		return (Arrays.binarySearch(nextIdModules, key) >= 0);		
//	}

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
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Internal compiler error --- Cannot find configuration.", 
					node.getFilename(), node.getLocation()));
		}
		return result.get(0);
	}
	
	public static Term defaultTerm(Term v) {
		String sort = v.getSort();
		if (!isKSort(sort)) sort = "K";
		if (!"K".equals(sort)) {
			sort = mainSort.get(sort);
		}
		if (isDefaulable(sort)) return new Empty(sort);
		GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
				KExceptionGroup.COMPILER, 
				"Don't know the default value for term " + v.toString() + ". Assuming .K", 
				v.getFilename(), v.getLocation()));
		return new Empty("K");
	}
	
	public static Term kWrapper(Term t) {
		if (DefinitionHelper.isSubsortedEq("K",t.getSort())) return t;
		return new KApp(new KInjectedLabel(t), new ListOfK());
	}

	public static boolean isKSort(String sort) {
		return (Arrays.binarySearch(kSorts, sort) >= 0);		
	}
		
	public static boolean isDefaulable(String sort) {
		return (Arrays.binarySearch(defaultableSorts, sort) >= 0);		
	}
	
	public static boolean isAnywhere(Rule r) {
		Attributes attrs = r.getAttributes();
		if (null == attrs) return false;
		for (Attribute any : anywheres) {
			if (any.getValue() == attrs.get(any.getKey())) return true;
		}
		return false;
	}
	
	public static Term kWrap(Term t) {
		return wrap(t, "k", "right");
	}
	
	public static Term wrap(Term t, String label, String ellipses) {
		Cell cell = new Cell();
		cell.setLabel(label);
		cell.setElipses(ellipses);
		cell.setContents(t);
		return cell;		
	}

	public static Variable freshVar(Set<Variable> vars, String sort) {
		String prefix = "?";
		int i = 0;
		Variable v = new Variable(prefix+i,sort);
		while (vars.contains(v)) {
			v.setName(prefix+(++i));
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
				if(10 / 0 == 0) return;
			}
		};
		try {
			t.accept(cellFinder);
		} catch (ArithmeticException e) {
			return true;
		}
		return false;
	}

	public static String getMaudeConstructor(String sort) {
		return maudeCollectionConstructors.get(sort);
	}
	
	public static Variable getFreshVar(String sort) {
		return new Variable("GeneratedFreshVar" + nextVarId++, sort);
	}

	public static Term getTerm(Production prod) {
		if (prod.isSubsort()) return getFreshVar(prod.getItems().get(0).toString());
//		if (prod.isConstant()) return new Constant(prod.getSort(), prod.getItems().toString());
		TermCons t = new TermCons(prod.getSort(), prod.getCons());
		if (prod.isListDecl()) {
			t.getContents().add(getFreshVar(((UserList)prod.getItems().get(0)).getSort()));
			t.getContents().add(getFreshVar(prod.getSort()));
			return t;
		}
		for (ProductionItem item : prod.getItems()) {
			if (item.getType() == ProductionType.SORT) {
				t.getContents().add(getFreshVar(((Sort)item).getName()));
			}
		}
		return t;
	}

	public static boolean isAnonVar(Variable node) {
		return node.getName().startsWith(anyVarSymbol);
	}

	public static boolean isBuiltinSort(String sort) {
		return (Arrays.binarySearch(builtinSorts, sort) >= 0);		
	}

	public static boolean isSyntaxSort(String name) {
		return ("K".equals(name) || !isKSort(name));
	}
	
	
	
}
