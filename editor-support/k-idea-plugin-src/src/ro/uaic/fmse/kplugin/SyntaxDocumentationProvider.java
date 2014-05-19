// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin;

import com.intellij.lang.documentation.DocumentationProvider;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiManager;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.KPsiUtil;
import ro.uaic.fmse.kplugin.psi.KSort;
import ro.uaic.fmse.kplugin.psi.KSyntax;

import java.util.List;

/**
 * @author Denis Bogdanas
 *         Created on 12/21/13.
 */
public class SyntaxDocumentationProvider implements DocumentationProvider {

    @Nullable
    @Override
    public String getQuickNavigateInfo(PsiElement element, PsiElement originalElement) {
        if (element instanceof KSyntax) {
            return DocumentationUtil.getFormattedModuleItemAndComment((KSyntax) element).toString();
        }
        return null;

    }

    @Nullable
    @Override
    public String generateDoc(PsiElement element, @Nullable PsiElement originalElement) {
        if (element instanceof KSyntax) {
            KSort sort = ((KSyntax) element).getSort();
            StringBuilder sb = new StringBuilder();

            for (KSyntax syntax : KPsiUtil.findSyntaxDefs(sort)) {
                if (sb.length() > 0) {
                    sb.append("\n\n");
                }
                sb.append(DocumentationUtil.getFormattedModuleItemAndComment(syntax));
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
