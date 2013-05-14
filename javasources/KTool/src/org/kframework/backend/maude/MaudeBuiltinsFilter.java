package org.kframework.backend.maude;

import org.kframework.backend.BackendFilter;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.utils.StringUtil;

import java.util.Properties;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/17/12
 * Time: 6:22 PM
 */
public class MaudeBuiltinsFilter extends BackendFilter {
	private String left, right;
	private boolean first;
	private final Properties builtinsProperties;

	public MaudeBuiltinsFilter(Properties builtinsProperties, DefinitionHelper definitionHelper) {
		super(definitionHelper);
		this.builtinsProperties = builtinsProperties;
	}

	@Override
	public void visit(Configuration node) {
		return;
	}

	@Override
	public void visit(Context node) {
		return;
	}

	@Override
	public void visit(Rule node) {
		return;
	}

	@Override
	public void visit(Production node) {
		if (!node.containsAttribute("hook")) {
			return;
		}
		final String hook = node.getAttribute("hook");
		if (builtinsProperties.containsKey(hook)) {
			result.append(builtinsProperties.getProperty(hook));
			result.append("\n");
			return;
		}
		result.append(" eq ");
		left = StringUtil.escapeMaude(node.getKLabel()) + "(";
		right = getHookLabel(hook) + "(";
		first = true;
		super.visit(node);
		left += ")";
		right += ")";
		result.append(left);
		result.append(" = _`(_`)(# ");
		result.append(right);
		result.append(", .KList) .\n");
	}


	@Override
	public void visit(Sort node) {
		if (!first) {
			left += ",, ";
			right += ", ";
		} else {
			first = false;
		}
		String sort = "#" + node.getName();
		final Variable var = Variable.getFreshVar(sort);
        MaudeFilter filter = new MaudeFilter(definitionHelper);
		filter.visit(var);
		left += filter.getResult();
		right += var.toString();
	}

	private String getHookLabel(String hook) {
		return hook.split(":")[1];
	}
}
