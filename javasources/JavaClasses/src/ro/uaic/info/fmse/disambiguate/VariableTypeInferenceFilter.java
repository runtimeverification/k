package ro.uaic.info.fmse.disambiguate;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Sentence;
import ro.uaic.info.fmse.k.Variable;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class VariableTypeInferenceFilter extends BasicTransformer {

	public ASTNode transform(Sentence r) {

		CollectVariablesVisitor vars = new CollectVariablesVisitor();
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
								GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, v1.getFilename(), v1.getLocation(), 0));
							}
			}

			// check to see if the declared type fits everywhere
			if (varDecl.size() == 1) {
				Variable declVar1 = varDecl.iterator().next(); // the declared var
				for (Entry<String, java.util.List<Variable>> entryVars : varLoc.entrySet()) { // for each location of the variable
					boolean isSubsorted = false;
					for (Variable inPlaceVar : entryVars.getValue())
						if (DefinitionHelper.isSubsortedEq(inPlaceVar.getSort(), declVar1.getSort()))
							isSubsorted = true;

					if (!isSubsorted) {
						String wrongPlace = entryVars.getValue().get(0).getLocation();
						String msg = "Variable '" + declVar1.getName() + "' declared with sort: " + declVar1.getSort() + " does not fit at: " + wrongPlace;
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, declVar1.getFilename(), declVar1.getLocation(), 0));
					}
				}
				// everything ok means update the locations
				correctVariableSorts(varList, declVar1.getSort());
			} else {
				// when there aren't any variable declarations
				java.util.Set<Variable> isect = new HashSet<Variable>();
				// find the intersection of varLoc
				for (Variable var1 : varLoc.entrySet().iterator().next().getValue()) {
					// iterate over the first variable location
					boolean inAll = true;
					for (Entry<String, java.util.List<Variable>> varLocEntry : varLoc.entrySet()) { // iterate over each location
						if (!varLocEntry.getValue().contains(var1)) {
							inAll = false;
							break;
						}
					}
					if (inAll)
						isect.add(var1);
				}
				Variable varr = varLoc.entrySet().iterator().next().getValue().get(0);
				if (isect.size() == 0) {
					String msg = "Could not infer a sort for variable '" + varr.getName() + "' to match every location.";
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, varr.getFilename(), varr.getLocation(), 0));
				}

				Variable inferredVar = null;

				// if I have more than one possibility choose a maximum
				if (isect.size() > 1) {
					java.util.List<Variable> maxSorts = new ArrayList<Variable>();

					for (Variable vv1 : isect) {
						boolean maxSort = true;
						for (Variable vv2 : isect) {
							if (DefinitionHelper.isSubsorted(vv2.getSort(), vv1.getSort()))
								maxSort = false;
						}
						if (maxSort)
							maxSorts.add(vv1);
					}

					if (maxSorts.size() > 1) {
						String msg = "Could not infer a unique sort for variable '" + varr.getName() + "'.";
						msg += " Possible sorts: ";
						for (Variable vv1 : maxSorts)
							msg += vv1.getSort() + ", ";
						msg = msg.substring(0, msg.length() - 2);
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, varr.getFilename(), varr.getLocation(), 0));
					}

					if (maxSorts.size() == 1)
						inferredVar = maxSorts.get(0);
				} else if (isect.size() == 1)
					inferredVar = isect.iterator().next();

				if (inferredVar != null) {
					correctVariableSorts(varList, isect.iterator().next().getSort());
					String msg = "Variable '" + inferredVar.getName() + "' was not declared. Assuming sort " + inferredVar.getSort();
					GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, msg, varr.getFilename(), varr.getLocation(), 3));
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

	private void correctVariableSorts(java.util.List<Variable> vars, String sort) {
		for (Variable v : vars)
			v.setSort(sort);
	}
}
