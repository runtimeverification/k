package org.kframework.compile.checks;

import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.HashMap;
import java.util.Map;

/**
 * Checks that no two cells with the same name are declared in the configuration.
 */
public class CheckConfigurationCells extends BasicVisitor {

	Map<String,Cell> cells = new HashMap<String,Cell>();

	@Override
	public void visit(Configuration node) {
		cells.clear();
		super.visit(node);
	}

	public CheckConfigurationCells(org.kframework.kil.loader.Context context) {
		super("Check that configuration cells have unique names", context);
	}

	@Override
	public void visit(Syntax node) {
		return;
	}

	@Override
	public void visit(org.kframework.kil.Context node) {
		return;
	}

	@Override
	public void visit(Rule node) {
		return;
	}

	@Override
	public void visit(Cell node) {
		Cell cell = cells.get(node.getId());
		if (cell != null) {
			GlobalSettings.kem.register(new KException(KException.ExceptionType.ERROR,
					KException.KExceptionGroup.COMPILER,
					"Cell " + node.getId() + " found twice in configuration (once at " + cell.getLocation() + ").",
					getName(), node.getFilename(), node.getLocation()));
		}
		cells.put(node.getId(), node);
		super.visit(node);
	}
}