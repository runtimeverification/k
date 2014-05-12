// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi;

import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiNamedElement;
import com.intellij.psi.PsiReference;
import com.intellij.util.IncorrectOperationException;
import org.jetbrains.annotations.NonNls;
import org.jetbrains.annotations.NotNull;

/**
 * @author Denis Bogdanas
 *         Created on 12/14/13.
 */
public interface IKSortBase extends PsiElement {

    PsiElement setName(@NonNls @NotNull String name) throws IncorrectOperationException;
}
