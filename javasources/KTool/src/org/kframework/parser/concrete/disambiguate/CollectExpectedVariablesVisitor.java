package org.kframework.parser.concrete.disambiguate;

import java.util.*;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectExpectedVariablesVisitor extends BasicVisitor {
	public CollectExpectedVariablesVisitor(Context context) {
		super(context);
	}

	/**
	 * Each element in the list is a Mapping from variable name and a list of constraints for that variable.
	 * On each Ambiguity node, a cartesian product is created between the current List and each ambiguity variant.
	 */
	public List<Map<String, Set<String>>> vars = new ArrayList<Map<String, Set<String>>>();

	@Override
	public void visit(Ambiguity node) {
		List<Map<String, Set<String>>> newVars = new ArrayList<Map<String, Set<String>>>();
		for (Term t : node.getContents()) {
			CollectExpectedVariablesVisitor viz = new CollectExpectedVariablesVisitor(context);
			t.accept(viz);
			// create the split
			for (Map<String, Set<String>> elem : vars) { // for every local type restrictions
				for (Map<String, Set<String>> elem2 : viz.vars) { // create a combination with every ambiguity detected
					newVars.add(combine(elem, elem2));
				}
			}
			if (vars.size() == 0)
				newVars.addAll(viz.vars);
		}
		vars = newVars;
		visit((Term) node);
	}

	@Override
	public void visit(Variable var) {
		if (!var.isUserTyped() && !var.getName().equals(MetaK.Constants.anyVarSymbol)) {
			if (vars.isEmpty())
				vars.add(new HashMap<String, Set<String>>());
			for (Map<String, Set<String>> vars2 : vars)
				if (vars2.containsKey(var.getName())) {
					Set<String> lst = vars2.get(var.getName());
					boolean contains = false;
					for (String v : lst)
						if (v.equals(var))
							contains = true;
					if (!contains)
						lst.add(var.getExpectedSort());
				} else {
					java.util.Set<String> varss = new HashSet<String>();
					varss.add(var.getExpectedSort());
					vars2.put(var.getName(), varss);
				}
		}
	}

	private Map<String, Set<String>> duplicate(Map<String, Set<String>> in) {
		Map<String, Set<String>> newM = new HashMap<String, Set<String>>();
		for (Map.Entry<String, Set<String>> elem : in.entrySet()) {
			newM.put(elem.getKey(), new HashSet<String>(elem.getValue()));
		}
		return newM;
	}

	private Map<String, Set<String>> combine(Map<String, Set<String>> in1, Map<String, Set<String>> in2) {
		Map<String, Set<String>> newM = duplicate(in1);
		for (Map.Entry<String, Set<String>> elem : in2.entrySet()) {
			if (newM.containsKey(elem.getKey()))
				newM.get(elem.getKey()).addAll(elem.getValue());
			else
				newM.put(elem.getKey(), new HashSet<String>(elem.getValue()));
		}
		return newM;
	}
}
