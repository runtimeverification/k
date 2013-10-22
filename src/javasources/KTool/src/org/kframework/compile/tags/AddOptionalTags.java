package org.kframework.compile.tags;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.general.GlobalSettings;

public class AddOptionalTags extends BasicTransformer {

	public AddOptionalTags(Context context) {
		super("AddOptionalTags", context);
	}

	@Override
	public ASTNode transform(Attributes node) throws TransformerException {

		for (String tag : GlobalSettings.transition)
			if (node.containsKey(tag))
				node.set("transition", "");
		for (String tag : GlobalSettings.supercool)
			if (node.containsKey(tag))
				node.set("supercool", "");
		for (String tag : GlobalSettings.superheat)
			if (node.containsKey(tag))
				node.set("superheat", "");

		return node;
	}
}
