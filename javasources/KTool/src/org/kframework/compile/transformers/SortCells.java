package org.kframework.compile.transformers;

import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 2/6/13
 * Time: 6:03 PM
 */
public class SortCells extends CopyOnWriteTransformer {

	private ConfigurationStructureMap config;

	public SortCells() {
		super("SortCells");
	}

	public SortCells(ConfigurationStructureMap config) {
		this();
		this.config = config;
	}

	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		ConfigurationStructure cfgStr = config.get(node);
		if (cfgStr.sons.isEmpty()) {
			return super.transform(node);
		}
		Term contents = node.getContents();
		if (contents instanceof Variable
                || contents instanceof KLabelConstant
                || contents instanceof Constant
                || contents instanceof Builtin)
            return node;
		return super.transform(node);    //To change body of overridden methods use File | Settings | File Templates.
	}
}
