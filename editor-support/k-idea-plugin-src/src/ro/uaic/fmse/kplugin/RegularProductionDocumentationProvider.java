// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin;

import com.intellij.lang.documentation.DocumentationProvider;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiManager;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.IModuleItem;
import ro.uaic.fmse.kplugin.psi.KPsiUtil;
import ro.uaic.fmse.kplugin.psi.KRegularProduction;

import java.util.List;

/**
 * @author Denis Bogdanas
 *         Created on 12/21/13.
 */
public class RegularProductionDocumentationProvider implements DocumentationProvider {

    @Nullable
    @Override
    public String getQuickNavigateInfo(PsiElement element, PsiElement originalElement) {
        if ((element instanceof KRegularProduction)) {
            return DocumentationUtil.getFormattedSyntaxDef((KRegularProduction) element).toString();
        }
        return null;

    }

    @Nullable
    @Override
    public String generateDoc(PsiElement element, @Nullable PsiElement originalElement) {
        if ((element instanceof KRegularProduction)) {
            KRegularProduction production = (KRegularProduction) element;
            StringBuilder sb = DocumentationUtil.getFormattedSyntaxAndComment(production);

            for (IModuleItem moduleItem : KPsiUtil.getImplementationRulesAndContexts(production)) {
                sb.append("\n\n").append(DocumentationUtil.getFormattedModuleItemAndComment(moduleItem));
            }
            String result = sb.toString().replace("\n", "<br/>");
            return result;
        } else {
            return null;
        }
    }

    @Nullable
    @Override
    public List<String> getUrlFor(PsiElement element, PsiElement originalElement) {
        return null;
    }

    @Nullable
    @Override
    public PsiElement getDocumentationElementForLookupItem(PsiManager psiManager, Object object, PsiElement element) {
        return null;
    }

    @Nullable
    @Override
    public PsiElement getDocumentationElementForLink(PsiManager psiManager, String link, PsiElement context) {
        return null;
    }
}
