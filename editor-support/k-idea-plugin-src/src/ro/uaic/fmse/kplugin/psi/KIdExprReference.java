// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi;

import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiReferenceBase;
import com.intellij.psi.ResolveResult;
import com.intellij.util.IncorrectOperationException;
import org.jetbrains.annotations.NotNull;

/**
 * @author Denis Bogdanas
 *         Created on 12/11/13.
 */
public class KIdExprReference extends PsiReferenceBase.Poly<IKIdExprBase> {
    /*Warning: Using multiple reference targets is not recommended.
    */

    private String name;

    public KIdExprReference(@NotNull IKIdExprBase element) {
        super(element, new TextRange(0, element.getTextLength()), true);
        name = element.getText();
    }

    @NotNull
    @Override
    public ResolveResult[] multiResolve(boolean incompleteCode) {
        ResolveResult[] result = resolveRuleVar();
        result = result.length >= 1 ? result : KPsiUtil.resolveAuxFunctions(this, name);
        if (name.startsWith("is")) {
            result = result.length >= 1 ? result : KPsiUtil.resolveSyntax(this, name.substring(2));
        }
        return result;
    }

    @NotNull
    public ResolveResult[] resolveRuleVar() {
        return KPsiUtil.resolveRuleVar(this, name);
    }

    @NotNull
    @Override
    public Object[] getVariants() {
        return new Object[0];
    }

    @Override
    public PsiElement handleElementRename(String newElementName) throws IncorrectOperationException {
        return getElement().setName(newElementName);
    }
}
