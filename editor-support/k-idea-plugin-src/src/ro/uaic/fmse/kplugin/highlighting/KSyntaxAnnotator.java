// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.highlighting;

import com.intellij.lang.ASTNode;
import com.intellij.lang.annotation.AnnotationHolder;
import com.intellij.lang.annotation.Annotator;
import com.intellij.openapi.editor.colors.TextAttributesKey;
import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiErrorElement;
import com.intellij.psi.ResolveResult;
import com.intellij.psi.tree.TokenSet;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.psi.*;

public class KSyntaxAnnotator implements Annotator {
    @Override
    public void annotate(@NotNull final PsiElement element, @NotNull AnnotationHolder holder) {
        if (element instanceof KAttributeBlock) {
            createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.ATTRIBUTE_BLOCK);

        } else if ((element instanceof KItemName &&
                (element.getParent() instanceof KModule || element.getParent() instanceof KImports))
                || element instanceof KRuleName) {
            createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.ITEM_NAME);

        } else if (element instanceof KCell) {
            KCellStart cellStart = ((KCell) element).getCellStart();
            if (cellStart != null) {
                int firstSpace = cellStart.getText().indexOf(' ');
                TextRange textRange = cellStart.getTextRange();
                if (firstSpace == -1) {
                    createAnnotation(holder, textRange, KSyntaxHighlighter.CELL);
                } else {
                    TextRange cellStartStartRange
                            = new TextRange(textRange.getStartOffset(), textRange.getStartOffset() + firstSpace);
                    createAnnotation(holder, cellStartStartRange, KSyntaxHighlighter.CELL);
                    TextRange cellStartEndRange = new TextRange(textRange.getEndOffset() - 1, textRange.getEndOffset());
                    createAnnotation(holder, cellStartEndRange, KSyntaxHighlighter.CELL);
                }
            }
            KCellEnd cellEnd = ((KCell) element).getCellEnd();
            if (cellEnd != null) {
                createAnnotation(holder, cellEnd.getTextRange(), KSyntaxHighlighter.CELL);
            }

        } else if (element instanceof KSort) {
            createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.TYPE);
        } else if (element instanceof KColon) {
            createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.COLON);
        } else if (element instanceof KVarDec && ((KVarDec) element).getId() != null) {
            //highlight variables, not underscores
            createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.VAR);

        } else if (element instanceof KIdExpr) {
            //highlight variable references
            @SuppressWarnings("ConstantConditions")
            ResolveResult[] resolveResults = ((KIdExprReference) element.getReference()).resolveRuleVar();
            if (resolveResults.length >= 1) {
                createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.VAR);
            } else {
                createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.FUNCTION_CALL);
            }
        } else if (element instanceof KSyntaxRhsAuxFunction) {
            KId id = ((KSyntaxRhsAuxFunction) element).getId();
            if (id != null) {
                createAnnotation(holder, id.getTextRange(), KSyntaxHighlighter.FUNCTION_DECLARATION);
            }
            for (ASTNode child : element.getNode()
                    .getChildren(TokenSet.create(KTypes.COMMA, KTypes.LEFT_PAREN, KTypes.RIGHT_PAREN))) {
                createAnnotation(holder, child.getTextRange(), KSyntaxHighlighter.FUNCTION_DECLARATION);
            }
        } else if (element instanceof PsiErrorElement || element instanceof KOtherItemBody) {
            createAnnotation(holder, element.getTextRange(), KSyntaxHighlighter.ERROR);
        }
    }

    private static void createAnnotation(AnnotationHolder holder, TextRange textRange,
                                         TextAttributesKey textAttributes) {
        holder.createInfoAnnotation(textRange, null).setTextAttributes(textAttributes);
    }
}
