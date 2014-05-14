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
 *         Altouugh this class is Poly, actually this reference resolves to just one target.
 */
public class KRegularProductionReference extends PsiReferenceBase.Poly<KRegularProduction> {

    private String name;

    public KRegularProductionReference(@NotNull KRegularProduction element) {
        super(element, element.getNameRangeInElement(), true);
        name = element.getName();
    }

    @NotNull
    @Override
    public ResolveResult[] multiResolve(boolean incompleteCode) {
        return KPsiUtil.resolveAuxFunctions(this, name);
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

    /**
     * If the constructor range argument was null, this reference have no range.
     */
    @Override
    protected TextRange calculateDefaultRangeInElement() {
        return getElement().getNameRangeInElement();
    }

    @Override
    public String toString() {
        return "KRegularProductionReference{" +
                "name='" + name + '\'' +
                '}';
    }
}
