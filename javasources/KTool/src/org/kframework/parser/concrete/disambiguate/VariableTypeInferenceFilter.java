package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Sentence;
import org.kframework.kil.Term;
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
		r = (Sentence) r.accept(new RemoveDuplicateVariables(context));

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
			if (!varDeclMap.containsKey(var.getName()))
				varDeclMap.put(var.getName(), var);
		}
		// after finding all of the variable declarations traverse the tree to disambiguate
		try {
			r = (Sentence) r.accept(new VariableTypeFilter(varDeclMap, false, context));
		} catch (TransformerException e) {
			e.report();
		}

		boolean varTypeInference = true;
		if (varTypeInference) {
			CollectExpectedVariablesVisitor vars2 = new CollectExpectedVariablesVisitor(context);
			r.accept(vars2);

			Set<VarHashMap> solutions = new HashSet<VarHashMap>();
			String fails = null;
			Set<String> failsAmb = null;
			String failsAmbName = null;
			for (VarHashMap variant : vars2.vars) {
				// take each solution and do GLB on every variable
				VarHashMap solution = new VarHashMap();
				for (Map.Entry<String, Set<String>> entry : variant.entrySet()) {
					Set<String> mins = new HashSet<String>();
					for (String sort : context.definedSorts) { // for every declared sort
						boolean min = true;
						for (String var : entry.getValue()) {
							if (!context.isSubsortedEq(var, sort)) {
								min = false;
								break;
							}
						}
						if (min)
							mins.add(sort);
					}
					if (mins.size() == 0) {
						fails = entry.getKey();
						break;
					} else if (mins.size() > 1) {
						java.util.Set<String> maxSorts = new HashSet<String>();

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
				if (!solution.isEmpty())
					solutions.add(solution);
			}
			if (!vars2.vars.isEmpty()) {
				if (solutions.size() == 0) {
					if (fails != null) {
						String msg = "Could not infer a sort for variable '" + fails + "' to match every location.";
						throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation()));
					} else {
						// Failure when in the same solutionn I can't find a unique sort for a specific variable.
						String msg = "Could not infer a unique sort for variable '" + failsAmbName + "'.";
						msg += " Possible sorts: ";
						for (String vv1 : failsAmb)
							msg += vv1 + ", ";
						msg = msg.substring(0, msg.length() - 2);
						throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation()));

					}
				} else if (solutions.size() == 1) {
					for (Map.Entry<String, Set<String>> entry : solutions.iterator().next().entrySet()) {
						Variable var = new Variable(entry.getKey(), null);
						var.setUserTyped(false);
						var.setExpectedSort(entry.getValue().iterator().next());
						var.setSyntactic(false);
						varDeclMap.put(entry.getKey(), var);
					}
					try {
						r = (Sentence) r.accept(new VariableTypeFilter(varDeclMap, true, context));
					} catch (TransformerException e) {
						e.report();
					}
					for (Map.Entry<String, Set<String>> solEntry : solutions.iterator().next().entrySet()) {
						String msg = "Variable '" + solEntry.getKey() + "' was not declared. Assuming sort " + solEntry.getValue().iterator().next();
						GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.COMPILER, msg, r.getFilename(), r.getLocation()));
					}
				} else {
					Map<String, Set<String>> collect = new HashMap<String, Set<String>>();
					for (VarHashMap sol : solutions) {
						for (Map.Entry<String, Set<String>> s : sol.entrySet())
							if (collect.containsKey(s.getKey())) {
								collect.get(s.getKey()).addAll(s.getValue());
							} else {
								collect.put(s.getKey(), new HashSet<String>(s.getValue()));
							}
					}
					for (Map.Entry<String, Set<String>> s : collect.entrySet()) {
						if (s.getValue().size() > 1) {
							String msg = "Could not infer a unique sort for variable '" + s.getKey() + "'.";
							msg += " Possible sorts: ";
							for (String vv1 : s.getValue())
								msg += vv1 + ", ";
							msg = msg.substring(0, msg.length() - 2);
							throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, r.getFilename(), r.getLocation()));
						}
					}
					// The above loop looks for variables that can have multiple sorts, collected from multiple solutions.
					// In rare cases (couldn't think of one right now) it may be that the
					// solution may be different because of different variable names
					assert false : "An error message should have been thrown here in the above loop.";
				}
			}
		}

		// type inference and error reporting
		// -- Error: type mismatch for variable... (when the declared variable doesn't fit everywhere)
		// -- Error: could not infer a sort for variable... (when there is no solution left)
		// -- Error: could not infer a unique sort for variable... (when there is more than one solution)
		// -- Warning: untyped variable, assuming sort...

		return r;
	}

	/**
	 * Removes ambiguities of the type amb(M:Map, M:MapItem)
	 * Chose the maximum
	 * @author Radu
	 *
	 */
	public class RemoveDuplicateVariables extends BasicTransformer {
		public RemoveDuplicateVariables(Context context) {
			super(RemoveDuplicateVariables.class.toString(), context);
		}

		public ASTNode transform(Ambiguity amb) throws TransformerException {
			Set<Term> maxterms = new HashSet<Term>();
			for (Term t : amb.getContents()) {
				if (t instanceof Variable) {
					// for variables only, find maximum
					boolean max = true;
					for (Term t1 : amb.getContents()) {
						if (t1 != t && t1 instanceof Variable && context.isSubsorted(t1.getSort(), t.getSort())) {
							max = false;
							break;
						}
					}
					if (max)
						maxterms.add(t);
				} else
					maxterms.add(t);
			}

			if (maxterms.size() == 1) {
				return maxterms.iterator().next().accept(this);
			} else if (maxterms.size() > 1)
				amb.setContents(new ArrayList<Term>(maxterms));

			return super.transform(amb);
		}
	}
}
