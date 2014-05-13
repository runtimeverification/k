// Copyright (c) 2014 K Team. All Rights Reserved.
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
public class KSyntaxBase extends ASTWrapperPsiElement implements IKSyntaxBase {
    public KSyntaxBase(@NotNull ASTNode node) {
        super(node);
    }

    @Nullable
    @Override
    public String getName() {
        return ((KSyntax) this).getSort().getText();
    }

    @Override
    public PsiElement setName(@NonNls @NotNull String newName) throws IncorrectOperationException {
        KSort sort = ((KSyntax) this).getSort();
        KSort newSort = KElementFactory.createSort(getProject(), newName);
        sort.replace(newSort);
        return this;
    }

    @Override
    public int getTextOffset() {
        KSort sort = ((KSyntax) this).getSort();
        return sort.getTextOffset();
    }

    @Override
    public int getTextLength() {
        return super.getTextLength();
    }

    @Nullable
    @Override
    public TextRange getNameRangeInElement() {
        KSort sort = ((KSyntax) this).getSort();
        return new TextRange(sort.getStartOffsetInParent(), sort.getTextLength());
    }

    @Override
    public ItemPresentation getPresentation() {
        return new SyntaxItemPresentation(this);
    }

}
