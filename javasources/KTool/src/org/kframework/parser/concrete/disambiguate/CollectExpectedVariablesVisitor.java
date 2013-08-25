package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectExpectedVariablesVisitor extends BasicVisitor {
	public CollectExpectedVariablesVisitor(Context context) {
		super(context);
		vars = new ArrayList<Map<String, List<Variable>>>();
		vars.add(new HashMap<String, List<Variable>>());
	}

	/**
	 * Each element in the list is a Mapping from variable name and a list of constraints for that variable.
	 * On each Ambiguity node, a cartesian product is created between the current List and each ambiguity variant.
	 */
	public List<Map<String, List<Variable>>> vars;

	@Override
	public void visit(Ambiguity node) {
		List<Map<String, List<Variable>>> newVars = new ArrayList<Map<String, List<Variable>>>();
		for (Term t : node.getContents()) {
			CollectExpectedVariablesVisitor viz = new CollectExpectedVariablesVisitor(context);
			t.accept(viz);
			// create the split
			for (Map<String, List<Variable>> elem : vars) { // for every local type restrictions
				for (Map<String, List<Variable>> elem2 : viz.vars) { // create a combination with every ambiguity detected
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
			for (Map<String, List<Variable>> vars2 : vars)
				if (vars2.containsKey(var.getName()))
					vars2.get(var.getName()).add(var);
				else {
					java.util.List<Variable> varss = new ArrayList<Variable>();
					varss.add(var);
					vars2.put(var.getName(), varss);
				}
		}
	}

	private Map<String, List<Variable>> duplicate(Map<String, List<Variable>> in) {
		Map<String, List<Variable>> newM = new HashMap<String, List<Variable>>();
		for (Map.Entry<String, List<Variable>> elem : in.entrySet()) {
			newM.put(elem.getKey(), new ArrayList<Variable>(elem.getValue()));
		}
		return newM;
	}

	private Map<String, List<Variable>> combine(Map<String, List<Variable>> in1, Map<String, List<Variable>> in2) {
		Map<String, List<Variable>> newM = duplicate(in1);
		for (Map.Entry<String, List<Variable>> elem : in2.entrySet()) {
			if (newM.containsKey(elem.getKey()))
				newM.get(elem.getKey()).addAll(elem.getValue());
			else
				newM.put(elem.getKey(), new ArrayList<Variable>(elem.getValue()));
		}
		return newM;
	}
}
