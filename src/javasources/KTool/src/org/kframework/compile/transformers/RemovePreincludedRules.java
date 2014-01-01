package org.kframework.compile.transformers;

import java.io.File;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.file.KPaths;


/**
 * 
 * @author YilongL
 */
public class RemovePreincludedRules extends CopyOnWriteTransformer {

	public RemovePreincludedRules(Context context) {
		super("Remove rules that are useless for the Java backend", context);
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
        if ((!node.getFilename().startsWith(KPaths.getKBase(false) + File.separator + "include") 
                && !node.getFilename().startsWith(org.kframework.kil.loader.Constants.GENERATED_FILENAME))
                || (node.getFilename().equals(KPaths.getKBase(false)
                        + File.separator + "include" + File.separator + "io"
                        + File.separator + "io.k"))                ) {
			return node;
		}

		return null;
	}
}
