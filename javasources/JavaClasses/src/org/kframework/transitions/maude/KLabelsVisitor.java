package org.kframework.transitions.maude;

import java.util.HashSet;
import java.util.Set;

import org.kframework.k.Constant;
import org.kframework.loader.Constants;
import org.kframework.visitors.BasicVisitor;


public class KLabelsVisitor extends BasicVisitor {

	public Set<String> kLabels = new HashSet<String>();

	@Override
	public void visit(Constant constant) {
		if (constant.getSort().equals(Constants.KLABEL))
			kLabels.add(constant.getValue());
		super.visit(constant);
	}
}
