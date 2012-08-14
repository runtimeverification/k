package ro.uaic.info.fmse.hkcd;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicVisitor;

/**
 * Transform AST of program into set of Haskell constructors.
 *
 * AST must not be processed by KAppModifier.
 *
 * @see ProgramLoader.loadPgmAst
 */
public class HaskellPgmFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	private String result = "";

	/**
	 * Update transformer state wrt type of current AST node.
	 *
	 * Parents handle parens.
	 */
	public void visit(TermCons tc) {
		String klabel =
			DefinitionHelper.conses.get("\"" + tc.getCons() + "\"")
			.getKLabel();
		result += "KApp (KLabel \"" + klabel + "\") [";

		int s = tc.getContents().size();

		if (s != 0)
			for (int i = 0; i < s; i++) {
				result += "(";
				tc.getContents().get(i).accept(this);
				result += ")";
				if (i < (s - 1))
					result += ", ";
			}

		result += "]";
	}

	public void visit(Constant cst) {
		String s = cst.getSort();
		String v = cst.getValue();

		if (s.equals("#Int")) {
			result += "KInt " + v;
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
