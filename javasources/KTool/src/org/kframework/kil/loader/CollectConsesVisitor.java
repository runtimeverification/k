package org.kframework.kil.loader;

import java.util.HashSet;
import java.util.Set;

import org.kframework.kil.Attribute;
import org.kframework.kil.Production;
import org.kframework.kil.visitors.BasicVisitor;

public class CollectConsesVisitor extends BasicVisitor {
	@Override
	public void visit(Production node) {
		if (node.containsAttribute(Constants.CONS_cons_ATTR)) {
			String cons = node.getAttribute(Constants.CONS_cons_ATTR);
			DefinitionHelper.conses.put(cons, node);
			DefinitionHelper.putLabel(node, cons);
		}
		if (node.isListDecl()) {
			DefinitionHelper.listConses.put(node.getSort(), node);
			DefinitionHelper.putListLabel(node);
		}
		for (Attribute a : node.getAttributes().getContents()) {
			String key = a.getKey();
			if (key.equals("klabel"))
				key = node.getAttribute("klabel");
			if (DefinitionHelper.productions.containsKey(key)) {
				DefinitionHelper.productions.get(key).add(node);
			} else {
				Set<Production> sset = new HashSet<Production>();
				sset.add(node);
				DefinitionHelper.productions.put(key, sset);
			}
		}
	}
}
