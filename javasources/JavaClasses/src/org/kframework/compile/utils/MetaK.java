package org.kframework.compile.utils;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.kframework.exceptions.TransformerException;
import org.kframework.k.ASTNode;
import org.kframework.k.Attribute;
import org.kframework.k.Attributes;
import org.kframework.k.Cell;
import org.kframework.k.Configuration;
import org.kframework.k.Context;
import org.kframework.k.Definition;
import org.kframework.k.Empty;
import org.kframework.k.KApp;
import org.kframework.k.KInjectedLabel;
import org.kframework.k.KSequence;
import org.kframework.k.ListItem;
import org.kframework.k.ListOfK;
import org.kframework.k.Map;
import org.kframework.k.MapItem;
import org.kframework.k.Production;
import org.kframework.k.ProductionItem;
import org.kframework.k.Rule;
import org.kframework.k.SetItem;
import org.kframework.k.Sort;
import org.kframework.k.Syntax;
import org.kframework.k.Term;
import org.kframework.k.TermCons;
import org.kframework.k.UserList;
import org.kframework.k.Variable;
import org.kframework.k.ProductionItem.ProductionType;
import org.kframework.loader.DefinitionHelper;
import org.kframework.visitors.BasicVisitor;
import org.kframework.visitors.CopyOnWriteTransformer;
import org.kframework.visitors.Visitable;
import org.kframework.visitors.Visitor;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

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
					node.getFilename(), node.getLocation(), 0));
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
				v.getFilename(), v.getLocation(), 0));
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
			public void visit(org.kframework.k.List node) {
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
			public void visit(org.kframework.k.Set node) {
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
		TermCons t = new TermCons(prod.getSort(), prod.getCons());
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
	
	
	
}
