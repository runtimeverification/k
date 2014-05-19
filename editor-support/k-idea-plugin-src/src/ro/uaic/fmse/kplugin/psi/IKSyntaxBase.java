// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi;

import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiNamedElement;
import org.jetbrains.annotations.Nullable;

/**
 * @author Denis Bogdanas
 *         Created on 12/15/13.
 */
public interface IKSyntaxBase extends PsiNamedElement, IModuleItem {

    @Nullable
    TextRange getNameRangeInElement();
}
