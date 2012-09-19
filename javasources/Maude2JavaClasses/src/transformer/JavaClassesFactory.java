package transformer;

import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Constant;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.List;
import org.kframework.kil.Map;
import org.kframework.kil.MapItem;
import org.kframework.kil.Set;

import basic.Term;

public class JavaClassesFactory {
	public static org.kframework.kil.Term getTerm(Term t) {
		if (t.getOp().equals("<_>_</_>") && t.getSort().equals("BagItem")) {
			Cell cl = new Cell("maude", "maude");
			Term cellLabel = t.getChildren().get(0);
			assert (cellLabel.getSort().equals("CellLabel"));
			cl.setLabel(cellLabel.getOp());

			cl.setContents((org.kframework.kil.Term) JavaClassesFactory.getTerm(t.getChildren().get(1)));
			cl.setElipses("none");

			return cl;
		}

		if (t.getOp().equals("__") && (t.getSort().equals("Bag") || t.getSort().equals("NeBag"))) {
			Bag bg = new Bag("maude", "maude");

			for (Term trm : t.getChildren())
				bg.getContents().add(JavaClassesFactory.getTerm(trm));

			return bg;
		}

		if (t.getOp().equals(".")) {
			Empty emp = new Empty("maude", "maude", t.getSort());
			assert (t.getChildren().size() == 0);
			return emp;
		}

		if (t.getOp().equals(".List`{K`}")) {
			Empty emp = new Empty("maude", "maude", "List{K}");
			assert (t.getChildren().size() == 0);
			return emp;
		}

		if (t.getOp().equals("__") && (t.getSort().equals("Map") || t.getSort().equals("NeMap"))) {
			Map mp = new Map("maude", "maude");

			for (Term trm : t.getChildren())
				mp.getContents().add(JavaClassesFactory.getTerm(trm));

			return mp;
		}

		if (t.getOp().equals("__") && (t.getSort().equals("Set") || t.getSort().equals("NeSet"))) {
			Set set = new Set("maude", "maude");

			for (Term trm : t.getChildren())
				set.getContents().add(JavaClassesFactory.getTerm(trm));

			return set;
		}

		if (t.getOp().equals("__") && (t.getSort().equals("List") || t.getSort().equals("NeList"))) {
			List lst = new List("maude", "maude");

			for (Term trm : t.getChildren())
				lst.getContents().add(JavaClassesFactory.getTerm(trm));

			return lst;
		}

		if (t.getOp().equals("_|->_") && t.getSort().equals("MapItem")) {
			MapItem mpi = new MapItem("maude", "maude");

			mpi.setKey(JavaClassesFactory.getTerm(t.getChildren().get(0)));
			mpi.setValue(JavaClassesFactory.getTerm(t.getChildren().get(1)));

			return mpi;
		}

		if (t.getOp().equals("_`(_`)") && t.getSort().equals("KItem")) {
			KApp kapp = new KApp("maude", "maude");
			kapp.setLabel(JavaClassesFactory.getTerm(t.getChildren().get(0)));
			kapp.setChild(JavaClassesFactory.getTerm(t.getChildren().get(1)));

			return kapp;
		}

		if (t.getOp().equals("#_") && t.getSort().equals("KLabel")) {
			KInjectedLabel kijl = new KInjectedLabel("maude", "maude");
			kijl.setTerm(JavaClassesFactory.getTerm(t.getChildren().get(0)));
			return kijl;
		}

		if (t.getOp().equals("#id_") && t.getSort().equals("#Id")) {
			Constant constant = new Constant("maude", "maude");
			constant.setSort("#Id");
			Term value = t.getChildren().get(0);
			assert (value.getSort().equals("#String") || value.getSort().equals("#Char"));
			constant.setValue(value.getOp().substring(1, value.getOp().length() - 1));
			return constant;
		}

		if (t.getSort().equals("#Zero")) {
			Constant constant = new Constant("maude", "maude");
			constant.setSort("#Int");
			constant.setValue("0");
			assert (t.getOp().equals("0"));
			return constant;
		}

		if (t.getSort().equals("#NzNat") && t.getOp().equals("sNat_")) {
			Constant constant = new Constant("maude", "maude");
			constant.setSort("#Int");
			constant.setValue(t.getNumber());
			assert (t.getChildren().get(0).getOp().equals("0"));
			assert (t.getChildren().get(0).getSort().equals("#Zero"));
			return constant;
		}

		/*
		 * if (Constants.LISTOFK.equals(element.getNodeName())) return new ListOfK(element); if (Constants.SETITEM.equals(element.getNodeName())) return new SetItem(element); if (Constants.BAGITEM.equals(element.getNodeName())) return new BagItem(element); if
		 * (Constants.CONST.equals(element.getNodeName())) return new Constant(element); if (Constants.KSEQUENCE.equals(element.getNodeName())) return new KSequence(element); if (Constants.HOLE.equals(element.getNodeName())) return new Hole(element); if
		 * (Constants.LISTITEM.equals(element.getNodeName())) return new ListItem(element);
		 */
		System.out.println(">>> " + t.getOp() + " sort: " + t.getSort() + " <<< - unimplemented yet: JavaClassesFactory - from maude Term");
		return null;
	}
}
