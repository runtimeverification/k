package org.kframework.backend.symbolic;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.file.KPaths;

/**
 * Tag all the rules which are not part of K "dist/include" files with
 * 'symbolic' attribute. All the rules tagged with symbolic will suffer the
 * symbolic execution transformation steps.
 * 
 * @author andreiarusoaie
 */
public class TagUserRules extends CopyOnWriteTransformer {

	List<String> notSymbolicTags = new ArrayList<String>(Arrays.asList(
			Constants.MACRO, Constants.STRUCTURAL, Constants.FUNCTION, SymbolicBackend.NOTSYMBOLIC));

	public TagUserRules(Context context) {
		super("Tag rules which are not builtin with 'symbolic' tag", context);
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {

		for (String nst : notSymbolicTags)
			if (node.containsAttribute(nst)) {
				return super.transform(node);
			}

		if (!node.getFilename().startsWith(
				KPaths.getKBase(false) + File.separator + "include")
				&& !node.getFilename().startsWith(
						org.kframework.kil.loader.Constants.GENERATED_FILENAME)) {
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
