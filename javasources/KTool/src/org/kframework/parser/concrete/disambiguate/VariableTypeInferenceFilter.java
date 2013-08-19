package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
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

		// for each variable name do checks or type inference
		for (Entry<String, java.util.List<Variable>> varEntry : vars.getVars().entrySet()) {
			java.util.List<Variable> varList = varEntry.getValue();

			// divide into locations
			Map<String, java.util.List<Variable>> varLoc = new HashMap<String, java.util.List<Variable>>();
			for (Variable var : varList) {
				if (varLoc.containsKey(var.getLocation()))
					varLoc.get(var.getLocation()).add(var);
				else {
					java.util.List<Variable> varss = new ArrayList<Variable>();
					varss.add(var);
					varLoc.put(var.getLocation(), varss);
				}
			}

			// get declarations (if any)
			java.util.Set<Variable> varDecl = new HashSet<Variable>();
			for (Variable var : varEntry.getValue()) {
				if (var.isUserTyped())
					varDecl.add(var);
			}

			// check to see if you have variable declarations with two different sorts
			if (varDecl.size() > 1) {
				for (Variable v1 : varDecl)
					for (Variable v2 : varDecl)
						if (v1 != v2)
							if (!v1.getSort().equals(v2.getSort())) {
								String msg = "Variable '" + v1.getName() + "' declared with two different sorts: " + v1.getSort() + " and " + v2.getSort();
								throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), v1.getFilename(), v1.getLocation()));
							}
			}

			// check to see if the declared type fits everywhere
			if (varDecl.size() == 1) {
				Map<String, Variable> varDeclMap = new HashMap<String, Variable>();
				Variable var = varDecl.iterator().next();
				varDeclMap.put(var.getName(), var);

				try {
					r = (Sentence) r.accept(new VariableTypeFilter(varDeclMap, context));
				} catch (TransformerException e) {
					e.report();
				}
			} else {
				// when there aren't any variable declarations
				java.util.Set<String> isect = new HashSet<String>();

				for (String sort : context.definedSorts) { // for every declared sort
					if (isect.contains(sort))
						continue;
					boolean inAll = true;
					for (Entry<String, java.util.List<Variable>> varLocEntry : varLoc.entrySet()) {
						// iterate over each location
						// to find a bottom sort that fits
						boolean inThisOne = false;
						for (Variable varLocEntry2 : varLocEntry.getValue()) {
							if (context.isSubsortedEq(varLocEntry2.getExpectedSort(), sort)) {
								inThisOne = true;
								break;
							}
						}
						if (!inThisOne) {
							inAll = false;
							break;
						}
					}
					if (inAll)
						isect.add(sort);
				}

				Variable varr = varLoc.entrySet().iterator().next().getValue().get(0);
				if (isect.size() == 0) {
					String msg = "Could not infer a sort for variable '" + varr.getName() + "' to match every location.";
					throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, varr.getFilename(), varr.getLocation()));
				}

				String inferredVar = null;

				// if I have more than one possibility choose a maximum
				if (isect.size() > 1) {
					java.util.List<String> maxSorts = new ArrayList<String>();

					for (String vv1 : isect) {
						boolean maxSort = true;
						for (String vv2 : isect) {
							if (context.isSubsorted(vv2, vv1))
								maxSort = false;
						}
						if (maxSort)
							maxSorts.add(vv1);
					}

					if (maxSorts.size() > 1) {
						String msg = "Could not infer a unique sort for variable '" + varr.getName() + "'.";
						msg += " Possible sorts: ";
						for (String vv1 : maxSorts)
							msg += vv1 + ", ";
						msg = msg.substring(0, msg.length() - 2);
						throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, varr.getFilename(), varr.getLocation()));
					}

					if (maxSorts.size() == 1)
						inferredVar = maxSorts.get(0);
				} else if (isect.size() == 1)
					inferredVar = isect.iterator().next();

				if (inferredVar != null) {
					Map<String, Variable> varDeclMap = new HashMap<String, Variable>();
					Variable varr2 = new Variable(varr.getName(), varr.getSort());
					varr2.setExpectedSort(inferredVar);
					varDeclMap.put(varr.getName(), varr2);

					try {
						r = (Sentence) r.accept(new VariableTypeFilterExpectedSort(varDeclMap, context));
					} catch (TransformerException e) {
						e.report();
					}

					String msg = "Variable '" + varr.getName() + "' was not declared. Assuming sort " + inferredVar;
					GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.COMPILER, msg, varr.getFilename(), varr.getLocation()));
				}
			}
			// type inference and error reporting
			// -- Error: type mismatch for variable... (when the declared variable doesn't fit everywhere)
			// -- Error: could not infer a sort for variable... (when the intersection is void)
			// -- Error: could not infer a unique sort for variable... (when there isn't a maximum sort in the intersection)
			// -- Warning: untyped variable, assuming sort...
		}

		return r;
	}
}
