package ro.uaic.info.fmse.transitions.maude;

import java.util.HashSet;
import java.util.Set;

import ro.uaic.info.fmse.k.Constant;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class KLabelsVisitor extends BasicVisitor {

	public Set<String> kLabels = new HashSet<String>();

	@Override
	public void visit(Constant constant) {
		if (constant.getSort().equals(Constants.KLABEL))
			kLabels.add(constant.getValue());
		super.visit(constant);
	}
}
