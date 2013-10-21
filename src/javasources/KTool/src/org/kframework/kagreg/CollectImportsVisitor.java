package org.kframework.kagreg;

import java.util.ArrayList;
import java.util.List;

import org.kframework.kil.Import;
import org.kframework.kil.Module;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectImportsVisitor extends BasicVisitor {
	protected List<Import> imports;
	protected boolean collectPredefined;
	protected int inPredefined;
	
	public CollectImportsVisitor(Context context, boolean collectPredefined) {
		super(context);
		imports = new ArrayList<Import>();
		this.collectPredefined = collectPredefined;
	}
	
	@Override
	public void visit(Module module) {
		if (module.isPredefined()) {
			inPredefined++;
		}
		super.visit(module);
		if (module.isPredefined()) {
			inPredefined--;
		}
	}
	
	@Override
	public void visit(Import node) {
		if (collectPredefined || inPredefined == 0) {
			imports.add(node);
		}
	}
	
	public List<Import> getImports() {
		return imports;
	}
}
