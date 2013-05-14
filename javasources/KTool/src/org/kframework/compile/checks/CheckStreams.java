package org.kframework.compile.checks;

import org.kframework.kil.Cell;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class CheckStreams extends BasicVisitor {

	public CheckStreams(DefinitionHelper definitionHelper) {
		super("Check Streaming Cell Contents", definitionHelper);
	}

	@Override
	public void visit(Cell node) {

		node.getContents().accept(this);
		String stream = node.getCellAttributes().get("stream");
		if (stream != null) {
			if (!definitionHelper.isSubsortedEq("List", node.getContents().getSort(definitionHelper))) {
				String msg = "Wrong sort in streaming cell. Expected List, but found " + node.getContents().getSort(definitionHelper) + ".";
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, getName(), node.getFilename(), node.getLocation()));
			}
		}
	}
}