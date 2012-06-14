package k3.loader;

import java.util.ArrayList;

import ro.uaic.info.fmse.k.Import;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class CollectIncludesVisitor extends BasicVisitor {
	private java.util.List<Import> importList = new ArrayList<Import>();

	public void visit(Import i) {
		importList.add(i);
	}

	public java.util.List<Import> getImportList() {
		return importList;
	}

	public void setImportList(java.util.List<Import> importList) {
		this.importList = importList;
	}
}
