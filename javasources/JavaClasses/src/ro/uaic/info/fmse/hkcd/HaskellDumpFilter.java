package ro.uaic.info.fmse.hkcd;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class HaskellDumpFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	private String result = "";

	@Override
	public void visit(Rule rule) {
		result += rule.getLabel() + endl;
	}

	public String getResult() {
		return result;
	}
}
