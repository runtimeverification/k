package ro.uaic.info.fmse.hkcd;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class HaskellFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	protected String result = "";

	public void visit(Constant cst) {
		String s = cst.getSort();
		String v = cst.getValue();

		result += "KApp (";

		// Perhaps we'd want to simply serialize some set of
		// classes into Haskell. This cannot be done with
		// existing set of Java classes for K since in Haskell
		// we have different constructors for various types of
		// constants, while in Java this information is stored
		// in the field of Constant class.
		if (s.equals("#Int")) {
			result += "KInt (" + v + ")";
		} else if (s.equals("#String")) {
			result += "KString " + v;
		} else if (s.equals("#Id")) {
			result += "KId \"" + v + "\"";
		} else if (s.equals("#Bool")) {
			result += "KBool " + HaskellUtil.capitalizeFirst(v);
		}

		result += ") []";
	}

	public void visit(Empty e) {
		result += "KApp (KLabel \"'." + e.getSort() + "\") []";
	}

	public String getResult() {
		return result;
	}
}
