package ro.uaic.info.fmse.compile.utils;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.Attribute;
import ro.uaic.info.fmse.k.Attributes;
import ro.uaic.info.fmse.k.Cell;
import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Context;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.KApp;
import ro.uaic.info.fmse.k.KInjectedLabel;
import ro.uaic.info.fmse.k.KSequence;
import ro.uaic.info.fmse.k.ListItem;
import ro.uaic.info.fmse.k.ListOfK;
import ro.uaic.info.fmse.k.Map;
import ro.uaic.info.fmse.k.MapItem;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.k.SetItem;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicVisitor;
import ro.uaic.info.fmse.visitors.Visitable;
import ro.uaic.info.fmse.visitors.Visitor;

public class MetaK {
	public class DoneException extends Exception {

	}

	public static String nextIdModules[] = {
		"SUBSTITUTION",
	};

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

	public static boolean isNextIdModule(String key) {
		return (Arrays.binarySearch(nextIdModules, key) >= 0);		
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
			public void visit(ro.uaic.info.fmse.k.List node) {
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
			public void visit(ro.uaic.info.fmse.k.Set node) {
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
}
