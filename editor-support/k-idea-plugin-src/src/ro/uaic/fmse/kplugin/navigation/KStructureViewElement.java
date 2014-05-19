// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.navigation;

import com.intellij.ide.structureView.StructureViewTreeElement;
import com.intellij.ide.util.treeView.smartTree.SortableTreeElement;
import com.intellij.ide.util.treeView.smartTree.TreeElement;
import com.intellij.navigation.ItemPresentation;
import com.intellij.navigation.NavigationItem;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiNamedElement;
import com.intellij.psi.util.PsiTreeUtil;
import ro.uaic.fmse.kplugin.psi.KFile;
import ro.uaic.fmse.kplugin.psi.KRegularProduction;
import ro.uaic.fmse.kplugin.psi.KSyntax;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class KStructureViewElement implements StructureViewTreeElement, SortableTreeElement {
    private PsiElement element;

    public KStructureViewElement(PsiElement element) {
        this.element = element;
    }

    @Override
    public Object getValue() {
        return element;
    }

    @Override
    public void navigate(boolean requestFocus) {
        if (element instanceof NavigationItem) {
            ((NavigationItem) element).navigate(requestFocus);
        }
    }

    @Override
    public boolean canNavigate() {
        return element instanceof NavigationItem &&
                ((NavigationItem) element).canNavigate();
    }

    @Override
    public boolean canNavigateToSource() {
        return element instanceof NavigationItem &&
                ((NavigationItem) element).canNavigateToSource();
    }

    @Override
    public String getAlphaSortKey() {
        return element instanceof PsiNamedElement ? ((PsiNamedElement) element).getName() : null;
    }

    @Override
    public ItemPresentation getPresentation() {
        return element instanceof NavigationItem ?
                ((NavigationItem) element).getPresentation() : null;
    }

    @Override
    public TreeElement[] getChildren() {
        if (element instanceof KFile) {
            @SuppressWarnings("unchecked")
            Collection<PsiNamedElement> elements =
                    PsiTreeUtil.findChildrenOfAnyType(element, KSyntax.class, KRegularProduction.class);
            List<TreeElement> treeElements = new ArrayList<>(elements.size());
            List<String> names = new ArrayList<>();
            for (PsiNamedElement element : elements) {
                String name = element.getName();
                if (name != null && !names.contains(name)) {
                    names.add(name);
                    treeElements.add(new KStructureViewElement(element));
                }
            }
            return treeElements.toArray(new TreeElement[treeElements.size()]);
        } else {
            return EMPTY_ARRAY;
        }
    }
}
