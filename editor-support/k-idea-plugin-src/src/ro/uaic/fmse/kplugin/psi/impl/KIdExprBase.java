// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiReference;
import com.intellij.util.IncorrectOperationException;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.psi.IKIdExprBase;
import ro.uaic.fmse.kplugin.psi.KElementFactory;
import ro.uaic.fmse.kplugin.psi.KIdExprReference;

/**
 * @author Denis Bogdanas
 *         Created on 12/14/13.
 */
public class KIdExprBase extends ASTWrapperPsiElement implements IKIdExprBase {

    public KIdExprBase(@NotNull ASTNode node) {
        super(node);
    }

    @Override
    @NotNull
    public PsiReference getReference() {
        return new KIdExprReference(this);
    }

    @Override
    public String getName() {
        return getText();
    }

    @Override
    public PsiElement setName(@NonNls @NotNull String name) throws IncorrectOperationException {
        KIdExprBase newExpr = KElementFactory.createIdInExpr(getProject(), name);
        return replace(newExpr);
    }
}
