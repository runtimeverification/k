package ro.uaic.fmse.kplugin;

import com.intellij.lang.ASTNode;
import com.intellij.psi.PsiComment;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiWhiteSpace;
import org.apache.commons.lang.StringEscapeUtils;
import ro.uaic.fmse.kplugin.psi.*;

/**
 * @author Denis Bogdanas
 *         Created on 23/02/14.
 */
public class DocumentationUtil {
    private DocumentationUtil() {
    }


    private static CharSequence formatSortsAndWhitespaces(ASTNode element) {
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

    private static String getEncodedText(ASTNode child) {
        return StringEscapeUtils.escapeHtml(child.getText());
    }

    static StringBuilder getFormattedSyntaxDef(KRegularProduction production) {
        KSyntax syntaxDec = (KSyntax) production.getParent().getParent();
        StringBuilder sb = new StringBuilder();

        return sb.append("<tt><b>syntax</b> <b>").append(syntaxDec.getSort().getText()).append("</b> ::= ")
                .append(formatSortsAndWhitespaces(production.getNode())).append("</tt>");
    }

    static StringBuilder getFormattedSyntaxAndComment(KRegularProduction production) {
        StringBuilder sb = getFormattedSyntaxDef(production);
        KSyntax syntaxDec = (KSyntax) production.getParent().getParent();
        String formattedComment = getAssociatedComment(syntaxDec);
        sb.insert(0, formattedComment);
        return sb;
    }

    private static String getAssociatedComment(PsiElement element) {
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

    static CharSequence getFormattedModuleItemAndComment(IModuleItem moduleItem) {
        StringBuilder sb = new StringBuilder().append(getFormattedKElement(moduleItem));
        String formattedComment = getAssociatedComment(moduleItem);
        sb.insert(0, formattedComment);
        return sb;
    }

    private static CharSequence getFormattedKElement(PsiElement element) {
        return new StringBuilder().append("<tt>").append(formatSortsAndWhitespaces(element.getNode())).append("</tt>");
    }
}
