package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Sentence;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class VariableTypeInferenceFilter extends BasicTransformer {

	public VariableTypeInferenceFilter(Context context) {
		super("Variable type inference", context);
	}

	@Override
	public ASTNode transform(Sentence r) throws TransformerException {

		CollectVariablesVisitor vars = new CollectVariablesVisitor(context);
		r.accept(vars);

		Map<String, Variable> varDeclMap = new HashMap<String, Variable>();
		// for each variable name do checks or type errors
		for (Entry<String, java.util.List<Variable>> varEntry : vars.getVars().entrySet()) {
			java.util.List<Variable> varList = varEntry.getValue();

			// check to see if you have variable declarations with two different sorts
			if (varList.size() > 1) {
				for (Variable v1 : varList) {
					for (Variable v2 : varList)
						if (v1 != v2)
							if (!v1.getSort().equals(v2.getSort())) {
								String msg = "Variable '" + v1.getName() + "' declared with two different sorts: " + v1.getSort() + " and " + v2.getSort();
								throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), v1.getFilename(), v1.getLocation()));
							}
					// if there are more than one declaration then prefer the one that is semantically typed
					if (!v1.isSyntactic()) {
						varDeclMap.put(v1.getName(), v1);
					}
				}
			}
			// if no semantic casts were found, then just choose the first syntactic restriction
			Variable var = varList.iterator().next();
			if (varDeclMap.containsKey(var.getName()))
				varDeclMap.put(var.getName(), var);
		}
		// after finding all of the variable declarations traverse the tree to disambiguate
		try {
			r = (Sentence) r.accept(new VariableTypeFilter(varDeclMap, context));
		} catch (TransformerException e) {
			e.report();
		}

		boolean varTypeInference = true;
		if (varTypeInference) {
			CollectExpectedVariablesVisitor vars2 = new CollectExpectedVariablesVisitor(context);
			r.accept(vars2);

			// TODO: GLUB for each variant
			List<Map<String, List<String>>> solutions = new ArrayList<Map<String, List<String>>>();
			String fails = null;
			List<String> failsAmb = null;
			String failsAmbName = null;
			for (Map<String, List<Variable>> variant : vars2.vars) {
				// take each solution and do GLUB on every variable
				Map<String, List<String>> solution = new HashMap<String, List<String>>();
				for (Map.Entry<String, List<Variable>> entry : variant.entrySet()) {
					List<String> mins = new ArrayList<String>();
					for (String sort : context.definedSorts) { // for every declared sort
						boolean min = true;
						for (Variable var : entry.getValue()) {
							if (!context.isSubsortedEq(var.getExpectedSort(), sort)) {
								min = false;
								break;
							}
						}
						if (min)
							mins.add(sort);
					}
					if (mins.size() == 0) {
						fails = entry.getKey();
						continue;
					} else if (mins.size() > 1) {
						java.util.List<String> maxSorts = new ArrayList<String>();

						for (String vv1 : mins) {
							boolean maxSort = true;
							for (String vv2 : mins)
								if (context.isSubsorted(vv2, vv1))
									maxSort = false;
							if (maxSort)
								maxSorts.add(vv1);
						}

						if (maxSorts.size() == 1)
							solution.put(entry.getKey(), maxSorts);
						else {
							failsAmb = maxSorts;
							failsAmbName = entry.getKey();
						}
					} else {
						solution.put(entry.getKey(), mins);
					}
				}
				// I found a solution that fits everywhere, then store it for disambiguation
				solutions.add(solution);
			}

			if (solutions.size() == 0) {
				if (fails != null) {
					String msg = "Could not infer a sort for variable '" + fails + "' to match every location.";
					throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation()));
				} else {
					String msg = "Could not infer a unique sort for variable '" + failsAmbName + "'.";
					msg += " Possible sorts: ";
					for (String vv1 : failsAmb)
						msg += vv1 + ", ";
					msg = msg.substring(0, msg.length() - 2);
					throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation()));

				}
			} else if (solutions.size() == 1) {
				try {
					r = (Sentence) r.accept(new VariableTypeFilter(varDeclMap, context));
				} catch (TransformerException e) {
					e.report();
				}
				for (Map.Entry<String, List<String>> solEntry : solutions.iterator().next().entrySet()) {
					String msg = "Variable '" + solEntry.getKey() + "' was not declared. Assuming sort " + solEntry.getValue().get(0);
					GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.COMPILER, msg, r.getFilename(), r.getLocation()));
				}
			} else {
				System.err.println("Multiple solutions in rule: " + r.getFilename() + ":" + r.getLocation());
			}
		}

		// type inference and error reporting
		// -- Error: type mismatch for variable... (when the declared variable doesn't fit everywhere)
		// -- Error: could not infer a sort for variable... (when the intersection is void)
		// -- Error: could not infer a unique sort for variable... (when there isn't a maximum sort in the intersection)
		// -- Warning: untyped variable, assuming sort...

		return r;
	}
}
