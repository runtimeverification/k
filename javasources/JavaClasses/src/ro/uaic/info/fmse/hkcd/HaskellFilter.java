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

		if (s.equals("#Int")) {
			result += "KInt (" + v + ")";
			return;
		}

		if (s.equals("#String")) {
			result += "KString " + v;
			return;
		}

		if (s.equals("#Id")) {
			result += "KId \"" + v + "\"";
			return;
		}


		if (s.equals("#Bool")) {
			result += "KBool " + HaskellUtil.capitalizeFirst(v);
			return;
		}
	}

	public String getResult() {
		return result;
	}
}
