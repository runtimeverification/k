// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiReference;
import com.intellij.util.IncorrectOperationException;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.psi.IKLabelBase;
import ro.uaic.fmse.kplugin.psi.KLabelReference;

/**
 * @author Denis Bogdanas
 *         Created on 12/14/13.
 */
public class KLabelBase extends ASTWrapperPsiElement implements IKLabelBase {

    public KLabelBase(@NotNull ASTNode node) {
        super(node);
    }

    @Override
    @NotNull
    public PsiReference getReference() {
        return new KLabelReference(this);
    }

    @Override
    public String getName() {
        return getText();
    }

    @Override
    public PsiElement setName(@NonNls @NotNull String name) throws IncorrectOperationException {
        throw new IncorrectOperationException("unsupported");
    }
}
