package org.kframework.backend.symbolic;

import java.util.Map;

import org.kframework.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Add variable $IN if the current cell is marked as being 
 * connected to the input stream.
 * @author andreiarusoaie
 *
 */
public class ResolveInputStreamCell extends CopyOnWriteTransformer {

	private boolean notSet = true;
	
	public ResolveInputStreamCell(Context context) {
		super("Resolve InputStream cell", context);
	}
	
	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		
		Map<String, String> attributes = node.getCellAttributes();
		if (!attributes.containsKey("stream"))
			return super.transform(node);
		
		if (node.getCellAttributes().get("stream").equals(Constants.STDIN) && notSet){
			Variable in = new Variable("$IN", "List");
			
			node.shallowCopy();
			node.setContents(in);
			notSet = true;
		}
		
		
		return super.transform(node);
	}
}
