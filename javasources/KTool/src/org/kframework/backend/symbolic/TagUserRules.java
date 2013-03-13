package org.kframework.backend.symbolic;

import java.io.File;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Rule;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.KPaths;

public class TagUserRules extends CopyOnWriteTransformer {

	public TagUserRules() {
		super("Tag rules which are not builtin with 'symbolic' tag");
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		
		if (!node.getFilename().startsWith(KPaths.getKBase(false) + File.separator + "include") && !node.getFilename().startsWith("File System"))
		{
			List<Attribute> attrs = node.getAttributes().getContents();
			attrs.add(new Attribute(SymbolicBackend.SYMBOLIC, ""));
			
			Attributes atts = node.getAttributes().shallowCopy();
			atts.setContents(attrs);
			
			node = node.shallowCopy();
			node.setAttributes(atts);
			return node;
		}
		return super.transform(node);
	}
}
