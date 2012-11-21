package org.kframework.parser.generator;

import org.kframework.kil.Import;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.ArrayList;


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
