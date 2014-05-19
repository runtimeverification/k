// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi.impl;

import com.intellij.extapi.psi.ASTWrapperPsiElement;
import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiReference;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.psi.IKVarDecBase;
import ro.uaic.fmse.kplugin.psi.KElementFactory;
import ro.uaic.fmse.kplugin.psi.KVarDec;
import ro.uaic.fmse.kplugin.psi.KVarDecReference;

/**
 * @author Denis Bogdanas
 *         Created on 12/11/13.
 */
public abstract class KVarDecBase extends ASTWrapperPsiElement implements IKVarDecBase {
    public KVarDecBase(@NotNull ASTNode node) {
        super(node);
    }

    public String getName() {
        return this.getText();
    }

    public PsiElement setName(@NotNull String newName) {
        KVarDec newVarDec = KElementFactory.createVarDec(getProject(), newName);
        return replace(newVarDec);
    }

    public PsiElement getNameIdentifier() {
        return this.getId();
    }

    @Override
    public PsiReference getReference() {
        return new KVarDecReference(this);
    }
}
