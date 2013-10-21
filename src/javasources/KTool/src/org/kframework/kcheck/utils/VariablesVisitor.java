package org.kframework.kcheck.utils;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class VariablesVisitor extends BasicVisitor {

	List<Variable> variables;
	
	public VariablesVisitor(Context context) {
		super(context);
		variables = new ArrayList<Variable>();
	}

	@Override
	public void visit(Variable node) {
		variables.add(node);
		super.visit(node);
	}
	
	public List<Variable> getVariables() {
		return variables;
	}
}
