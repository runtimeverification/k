package org.kframework.compile.checks;

import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class CheckStreams extends BasicVisitor {

	public CheckStreams() {
		super("Check Streaming Cell Contents");
	}
	
	@Override
	public void visit(Cell node) {

		node.getContents().accept(this);
		String stream = node.getCellAttributes().get("stream");
		if (stream != null) {
			if(KSort.getKSort(node.getContents().getSort()) != KSort.List) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
						KExceptionGroup.CRITICAL, 
						"Wrong sort in streaming cell. List is expected instead of " + node.getContents().getSort() + ".", 
						getName(), node.getFilename(), node.getLocation()));
			}
		}
	}
}