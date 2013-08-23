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

			//			// when there aren't any variable declarations
			//			java.util.Set<Variable> isect = new HashSet<Variable>();
			//			// find the intersection of varLoc
			//			for (Variable var1 : varLoc.entrySet().iterator().next().getValue()) {
			//				// iterate over the first variable location
			//				boolean inAll = true;
			//				for (Entry<String, java.util.List<Variable>> varLocEntry : varLoc.entrySet()) { // iterate over each location
			//					if (!varLocEntry.getValue().contains(var1)) {
			//						inAll = false;
			//						break;
			//					}
			//				}
			//				if (inAll)
			//					isect.add(var1);
			//			}
			//			Variable varr = varLoc.entrySet().iterator().next().getValue().get(0);
			//			if (isect.size() == 0) {
			//				String msg = "Could not infer a sort for variable '" + varr.getName() + "' to match every location.";
			//				throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, varr.getFilename(), varr.getLocation()));
			//			}
			//
			//			Variable inferredVar = null;
			//
			//			// if I have more than one possibility choose a maximum
			//			if (isect.size() > 1) {
			//				java.util.List<Variable> maxSorts = new ArrayList<Variable>();
			//
			//				for (Variable vv1 : isect) {
			//					boolean maxSort = true;
			//					for (Variable vv2 : isect) {
			//						if (context.isSubsorted(vv2.getSort(), vv1.getSort()))
			//							maxSort = false;
			//					}
			//					if (maxSort)
			//						maxSorts.add(vv1);
			//				}
			//
			//				if (maxSorts.size() > 1) {
			//					String msg = "Could not infer a unique sort for variable '" + varr.getName() + "'.";
			//					msg += " Possible sorts: ";
			//					for (Variable vv1 : maxSorts)
			//						msg += vv1.getSort() + ", ";
			//					msg = msg.substring(0, msg.length() - 2);
			//					throw new TransformerException(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, varr.getFilename(), varr.getLocation()));
			//				}
			//
			//				if (maxSorts.size() == 1)
			//					inferredVar = maxSorts.get(0);
			//			} else if (isect.size() == 1)
			//				inferredVar = isect.iterator().next();
			//
			//			if (inferredVar != null) {
			//				Map<String, Variable> varDeclMap = new HashMap<String, Variable>();
			//				varDeclMap.put(inferredVar.getName(), inferredVar);
			//
			//				try {
			//					r = (Sentence) r.accept(new VariableTypeFilter(varDeclMap, context));
			//				} catch (TransformerException e) {
			//					e.report();
			//				}
			//
			//				String msg = "Variable '" + inferredVar.getName() + "' was not declared. Assuming sort " + inferredVar.getSort();
			//				GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.COMPILER, msg, varr.getFilename(), varr.getLocation()));
			//			}
		}

		// type inference and error reporting
		// -- Error: type mismatch for variable... (when the declared variable doesn't fit everywhere)
		// -- Error: could not infer a sort for variable... (when the intersection is void)
		// -- Error: could not infer a unique sort for variable... (when there isn't a maximum sort in the intersection)
		// -- Warning: untyped variable, assuming sort...

		return r;
	}
}
