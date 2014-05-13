// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi.impl;

import com.intellij.navigation.ItemPresentation;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.KIcons;
import ro.uaic.fmse.kplugin.psi.KRegularProduction;
import ro.uaic.fmse.kplugin.psi.KSyntax;

import javax.swing.*;

/**
 * @author Denis Bogdanas
 *         Created on 12/18/13.
 */
class SyntaxItemPresentation implements ItemPresentation {
    private KSyntaxBase element;

    public SyntaxItemPresentation(KSyntaxBase element) {
        this.element = element;
    }

    @Nullable
    @Override
    public String getPresentableText() {
        return element.getName();
    }

    @Nullable
    @Override
    public String getLocationString() {
        return element.getContainingFile().getVirtualFile().getName();
    }

    @Nullable
    @Override
    public Icon getIcon(boolean unused) {
        return KIcons.FILE;
    }
}
