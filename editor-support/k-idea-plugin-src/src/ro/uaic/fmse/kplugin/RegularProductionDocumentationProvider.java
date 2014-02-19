package ro.uaic.fmse.kplugin;

import com.intellij.lang.ASTNode;
import com.intellij.lang.documentation.DocumentationProvider;
import com.intellij.psi.PsiComment;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiManager;
import com.intellij.psi.PsiWhiteSpace;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.KRegularProduction;
import ro.uaic.fmse.kplugin.psi.KSort;
import ro.uaic.fmse.kplugin.psi.KSyntax;

import java.util.List;

/**
 * @author Denis Bogdanas
 *         Created on 12/21/13.
 */
public class RegularProductionDocumentationProvider implements DocumentationProvider {

    @Nullable
    @Override
    public String getQuickNavigateInfo(PsiElement element, PsiElement originalElement) {
        if (!(element instanceof KRegularProduction)) {
            return null;
        }

        return getOriginalText((KRegularProduction) element);
    }

    private String getOriginalText(KRegularProduction element) {
        KSyntax syntaxDec = (KSyntax) element.getParent().getParent();

        return "syntax <b>" + syntaxDec.getSort().getText() + "</b> ::= " + getProductionQuickNavigateText(element);
    }

    private String getProductionQuickNavigateText(KRegularProduction element) {
        StringBuilder sb = new StringBuilder(element.getTextLength());
        for (ASTNode child : element.getNode().getChildren(null)) {
            if (child.getPsi() instanceof KSort) {
                sb.append("<b>").append(child.getText()).append("</b>");
            } else if (child.getPsi() instanceof PsiWhiteSpace) {
                sb.append(child.getText().replace(" ", "&nbsp;"));
            } else {
                sb.append(child.getText());
            }
        }
        return sb.toString();
    }

    @Nullable
    @Override
    public List<String> getUrlFor(PsiElement element, PsiElement originalElement) {
        return null;
    }

    @Nullable
    @Override
    public String generateDoc(PsiElement element, @Nullable PsiElement originalElement) {
        if (!(element instanceof KRegularProduction)) {
            return null;
        }
        String result = getQuickNavigateInfo(element, originalElement);
        KSyntax syntaxDec = (KSyntax) element.getParent().getParent();
        PsiElement prevNode = syntaxDec.getPrevSibling();
        if (prevNode instanceof PsiWhiteSpace && countNewLines(prevNode.getText()) <= 1) {
            prevNode = prevNode.getPrevSibling();
        }
        if (prevNode instanceof PsiComment) {
            String commentText = prevNode.getText();
            int startTrim;
            int endTrim;
            if (commentText.startsWith("/*@")) {
                startTrim = 3;
            } else {
                startTrim = 2;
            }
            if (commentText.startsWith("//")) {
                endTrim = 0;
            } else {
                endTrim = 2;
            }
            String trimmedComment = commentText.substring(startTrim, commentText.length() - endTrim).trim();
            String extraNewLines = "\n\n";
            result = trimmedComment + extraNewLines + result;
        }

        result = result != null ? result.replace("\n", "<br/>") : null;
        return result;
    }

    private static int countNewLines(String text) {
        int index = 0;
        int count = 0;
        while ((index = text.indexOf("\n", index)) >= 0) {
            count++;
            index++;
        }
        return count;
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
