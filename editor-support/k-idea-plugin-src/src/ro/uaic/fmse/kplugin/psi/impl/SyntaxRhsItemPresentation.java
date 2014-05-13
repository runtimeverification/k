// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi.impl;

import com.intellij.navigation.ItemPresentation;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.KIcons;
import ro.uaic.fmse.kplugin.psi.KRegularProduction;

import javax.swing.*;

/**
 * @author Denis Bogdanas
 *         Created on 12/18/13.
 */
class SyntaxRhsItemPresentation implements ItemPresentation {
    private KRegularProduction element;

    public SyntaxRhsItemPresentation(KRegularProduction element) {
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
