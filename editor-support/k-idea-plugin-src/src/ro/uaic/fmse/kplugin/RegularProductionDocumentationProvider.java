package ro.uaic.fmse.kplugin;

import com.intellij.lang.ASTNode;
import com.intellij.lang.documentation.DocumentationProvider;
import com.intellij.psi.PsiComment;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiManager;
import com.intellij.psi.PsiWhiteSpace;
import org.apache.commons.lang.StringEscapeUtils;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.*;

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

        return getFormattedSyntaxDef((KRegularProduction) element).toString();
    }

    @Nullable
    @Override
    public String generateDoc(PsiElement element, @Nullable PsiElement originalElement) {
        if (!(element instanceof KRegularProduction)) {
            return null;
        }
        KRegularProduction production = (KRegularProduction) element;
        StringBuilder sb = getFormattedSyntaxAndComment(production);

        for (KRule rule : KPsiUtil.getImplementationRules(production)) {
            sb.append("\n\n").append(getFormattedRuleAndComment(rule));
        }
        String result = sb.toString().replace("\n", "<br/>");
        return result;
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

    private CharSequence formatSortsAndWhitespaces(ASTNode element) {
        StringBuilder sb = new StringBuilder(element.getTextLength());
        for (ASTNode child : element.getChildren(null)) {
            if (child.getPsi() instanceof KSort || child.getElementType() == KTypes.KEYWORD ||
                    child.getPsi() instanceof KRuleName) {
                sb.append("<b>").append(child.getText()).append("</b>");
            } else if (child instanceof PsiWhiteSpace) {
                String text = child.getText();
                if (child.getTextLength() > 1) {
                    text = text.replace(" ", "&nbsp;");
                }
                sb.append(text);
            } else if (child instanceof PsiComment) {
                sb.append("<i>").append(getEncodedText(child)).append("</i>");
            } else if (child.getChildren(null).length == 0) {
                sb.append(getEncodedText(child));
            } else {
                sb.append(formatSortsAndWhitespaces(child));
            }
        }
        return sb;
    }

    private String getEncodedText(ASTNode child) {
        return StringEscapeUtils.escapeHtml(child.getText());
    }

    private StringBuilder getFormattedSyntaxDef(KRegularProduction production) {
        KSyntax syntaxDec = (KSyntax) production.getParent().getParent();
        StringBuilder sb = new StringBuilder();

        return sb.append("<tt><b>syntax</b> <b>").append(syntaxDec.getSort().getText()).append("</b> ::= ")
                .append(formatSortsAndWhitespaces(production.getNode())).append("</tt>");
    }

    private StringBuilder getFormattedSyntaxAndComment(KRegularProduction production) {
        StringBuilder sb = getFormattedSyntaxDef(production);
        KSyntax syntaxDec = (KSyntax) production.getParent().getParent();
        String formattedComment = getAssociatedComment(syntaxDec);
        sb.insert(0, formattedComment);
        return sb;
    }

    private String getAssociatedComment(PsiElement element) {
        String formattedComment = "";
        PsiElement prevNode = element.getPrevSibling();
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
            formattedComment = "<i>" + StringEscapeUtils.escapeHtml(trimmedComment) + extraNewLines + "</i>";
        }
        return formattedComment;
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

    private CharSequence getFormattedRuleAndComment(KRule rule) {
        StringBuilder sb = new StringBuilder().append(getFormattedRule(rule));
        String formattedComment = getAssociatedComment(rule);
        sb.insert(0, formattedComment);
        return sb;
    }

    private CharSequence getFormattedRule(KRule rule) {
        return new StringBuilder().append("<tt>").append(formatSortsAndWhitespaces(rule.getNode())).append("</tt>");
    }

}
