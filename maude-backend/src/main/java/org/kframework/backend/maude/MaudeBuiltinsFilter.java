// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.backend.maude;

import org.kframework.backend.BackendFilter;
import org.kframework.kil.Attribute;
import org.kframework.kil.Configuration;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.Sort;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.util.Properties;


/**
 * Visitor generating the maude equations hooking the builtins from the hooked productions.
 */
public class MaudeBuiltinsFilter extends BackendFilter {
    private String left, right;
    private boolean first;
    private final Properties maudeHooksMap;
    private final Properties specialMaudeHooks;
    private final KExceptionManager kem;

    public MaudeBuiltinsFilter(Properties maudeHooksMap, Properties specialMaudeHooks, Context context, KExceptionManager kem) {
        super(context);
        this.maudeHooksMap = maudeHooksMap;
        this.specialMaudeHooks = specialMaudeHooks;
        this.kem = kem;
    }

    @Override
    public Void visit(Configuration node, Void _) {
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _) {
        return null;
    }

    @Override
    public Void visit(Rule node, Void _) {
        return null;
    }

    @Override
    public Void visit(Production node, Void _) {
        if (!node.containsAttribute(Attribute.HOOK_KEY)) {
            return null;
        }
        final String hook = node.getAttribute(Attribute.HOOK_KEY);
        if (!maudeHooksMap.containsKey(hook)) {
            return null;
        }

        if (specialMaudeHooks.containsKey(hook)) {
            result.append(specialMaudeHooks.getProperty(hook));
            result.append("\n");
            return null;
        }

        result.append(" eq ");
        left = StringUtil.escapeMaude(node.getKLabel());
        left += "(";
        right = getHookLabel((String)maudeHooksMap.get(hook));
        if (node.getArity() > 0) {
            right += "(";
            first = true;
            super.visit(node, _);
            right += ")";
        } else {
            left += ".KList";
        }
        left += ")";
        result.append(left);
        result.append(" = _`(_`)(");
        if (context.getDataStructureSorts().containsKey(node.getSort())) {
            result.append(context.dataStructureSortOf(node.getSort()).type() + "2KLabel_(");
        } else {
            result.append("#_(");
        }
        result.append(right);
        result.append("), .KList)");
        result.append(" .\n");
        return null;
    }


    @Override
    public Void visit(NonTerminal node, Void _) {
        if (!first) {
            left += ",, ";
            right += ", ";
        } else {
            first = false;
        }

        Variable var;
        if (context.getDataStructureSorts().containsKey(node.getSort())
                || node.getSort().equals(Sort.K)
                || node.getSort().equals(Sort.KITEM)) {
            var = Variable.getAnonVar(node.getSort());
        } else {
            var = Variable.getAnonVar(Sort.of("#" + node.getName()));
        }

        MaudeFilter filter = new MaudeFilter(context, kem);
        filter.visit(var, null);
        left += filter.getResult();

        if (context.getDataStructureSorts().containsKey(node.getSort())) {
            var.setSort(context.dataStructureSortOf(node.getSort()).type());
        }
        right += var.toString();
        return null;
    }

    private String getHookLabel(String hook) {
        return hook.split(":")[1];
    }

}
