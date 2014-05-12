// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.usages;

import com.intellij.psi.PsiElement;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.usages.UsageTarget;
import com.intellij.usages.impl.rules.UsageType;
import com.intellij.usages.impl.rules.UsageTypeProviderEx;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.IModuleItem;
import ro.uaic.fmse.kplugin.psi.KContext;
import ro.uaic.fmse.kplugin.psi.KRule;
import ro.uaic.fmse.kplugin.psi.KSyntax;

/**
 * @author Denis Bogdanas
 *         Created on 12/16/13.
 */
public class KUsageTypeProvider implements UsageTypeProviderEx {

    private static UsageType SYNTAX_DEF = new UsageType("Syntax");
    private static UsageType RULE = new UsageType("Rule");
    private static UsageType CONTEXT = new UsageType("Context");

    @Nullable
    @Override
    public UsageType getUsageType(PsiElement element, @NotNull UsageTarget[] targets) {
        return getUsageType(element);
    }

    @Nullable
    @Override
    public UsageType getUsageType(PsiElement element) {
        IModuleItem moduleItem = PsiTreeUtil.getParentOfType(element, IModuleItem.class);
        if (moduleItem instanceof KSyntax) {
            return SYNTAX_DEF;
        } else if (moduleItem instanceof KRule) {
            return RULE;
        } else if (moduleItem instanceof KContext) {
            return CONTEXT;
        } else {
            return null;
        }
    }
}
