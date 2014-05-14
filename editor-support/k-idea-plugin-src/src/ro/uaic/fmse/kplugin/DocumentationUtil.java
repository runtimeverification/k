// Copyright (c) 2014 K Team. All Rights Reserved.
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


    private static void formatSortsAndWhitespaces(StringBuilder sb, ASTNode element) {
        if (element.getPsi() instanceof KSort || element.getElementType() == KTypes.KEYWORD ||
                element.getPsi() instanceof KRuleName) {
            sb.append("<b>").append(element.getText()).append("</b>");
        } else if (element instanceof PsiWhiteSpace) {
            String text = element.getText();
            if (element.getTextLength() > 1) {
                text = text.replace(" ", "&nbsp;");
            }
            sb.append(text);
        } else if (element instanceof PsiComment) {
            sb.append("<i>").append(getEncodedText(element)).append("</i>");
        } else if (element.getChildren(null).length == 0) {
            sb.append(getEncodedText(element));
        } else {
            for (ASTNode child : element.getChildren(null)) {
                formatSortsAndWhitespaces(sb, child);
            }
        }
    }

    private static String getEncodedText(ASTNode child) {
        return StringEscapeUtils.escapeHtml(child.getText());
    }

    static StringBuilder getFormattedSyntaxDef(KRegularProduction production) {
        KSyntax syntaxDec = (KSyntax) production.getParent();
        StringBuilder sb = new StringBuilder();

        sb.append("<tt><b>syntax</b> <b>").append(syntaxDec.getSort().getText()).append("</b> ::= ");
        formatSortsAndWhitespaces(sb, production.getNode());
        for (PsiElement trailingElem : KPsiUtil.getTrailingSpaceAndComment(production)) {
            formatSortsAndWhitespaces(sb, trailingElem.getNode());
        }
        return sb.append("</tt>");
    }

    static StringBuilder getFormattedSyntaxAndComment(KRegularProduction production) {
        StringBuilder sb = getFormattedSyntaxDef(production);
        KSyntax syntaxDec = (KSyntax) production.getParent();
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
            if (commentText.startsWith("/*@") || commentText.startsWith("//@")) {
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
            formattedComment = "<tt><i>" + StringEscapeUtils.escapeHtml(trimmedComment) + extraNewLines + "</i></tt>";
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
        StringBuilder sb = new StringBuilder();
        sb.append("<tt>");
        formatSortsAndWhitespaces(sb, element.getNode());
        for (PsiElement trailingElem : KPsiUtil.getTrailingSpaceAndComment(element)) {
            formatSortsAndWhitespaces(sb, trailingElem.getNode());
        }
        return sb.append("</tt>");
    }
}
