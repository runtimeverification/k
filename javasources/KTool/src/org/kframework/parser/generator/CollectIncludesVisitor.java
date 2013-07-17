package org.kframework.parser.generator;

import java.util.ArrayList;

import org.kframework.kil.Import;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectIncludesVisitor extends BasicVisitor {
	public CollectIncludesVisitor(Context context) {
		super(context);
	}

	private java.util.List<Import> importList = new ArrayList<Import>();

	public void visit(Import i) {
		importList.add(i);
	}

	public void visit(ModuleItem mi) {
	}

	public java.util.List<Import> getImportList() {
		return importList;
	}

	public void setImportList(java.util.List<Import> importList) {
		this.importList = importList;
	}
}
