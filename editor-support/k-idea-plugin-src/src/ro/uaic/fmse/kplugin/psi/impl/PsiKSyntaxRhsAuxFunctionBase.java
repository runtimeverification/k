// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.navigation.ItemPresentation;
import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiReference;
import com.intellij.util.IncorrectOperationException;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.*;

/**
 * @author Denis Bogdanas
 *         Created on 12/15/13.
 */
public class PsiKSyntaxRhsAuxFunctionBase extends ASTWrapperPsiElement implements KRegularProduction {
    public PsiKSyntaxRhsAuxFunctionBase(@NotNull ASTNode node) {
        super(node);
    }

    @Nullable
    @Override
    public String getName() {
        KId id = ((KSyntaxRhsAuxFunction) this).getId();
        return id != null ? id.getText() : null;
    }

    @Override
    public PsiElement setName(@NonNls @NotNull String newName) throws IncorrectOperationException {
        KId id = ((KSyntaxRhsAuxFunction) this).getId();
        if (id != null) {
            KId newId = KElementFactory.createId(getProject(), newName);
            id.replace(newId);
            return this;
        } else {
            throw new IncorrectOperationException();
        }
    }

    @Override
    public int getTextOffset() {
        KId id = ((KSyntaxRhsAuxFunction) this).getId();
        return id != null ? id.getTextOffset() : super.getTextOffset();
    }

    @Override
    public int getTextLength() {
        return super.getTextLength();
    }

    @Override
    public PsiReference getReference() {
        return getName() != null ? new KRegularProductionReference(this) : null;
    }

    @Nullable
    @Override
    public TextRange getNameRangeInElement() {
        KId id = ((KSyntaxRhsAuxFunction) this).getId();
        return id != null ? new TextRange(id.getStartOffsetInParent(), id.getTextLength()) : null;
    }

    @Override
    public ItemPresentation getPresentation() {
        return new SyntaxRhsItemPresentation(this);
    }

}
