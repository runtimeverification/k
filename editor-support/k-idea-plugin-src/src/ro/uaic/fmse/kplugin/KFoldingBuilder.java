// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin;

import com.intellij.lang.ASTNode;
import com.intellij.lang.folding.FoldingBuilderEx;
import com.intellij.lang.folding.FoldingDescriptor;
import com.intellij.openapi.editor.Document;
import com.intellij.openapi.editor.FoldingGroup;
import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiComment;
import com.intellij.psi.PsiElement;
import com.intellij.psi.util.PsiTreeUtil;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.IModuleItem;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * @author Denis Bogdanas
 *         Created on 12/15/13.
 */
public class KFoldingBuilder extends FoldingBuilderEx {
    @NotNull
    @Override
    public FoldingDescriptor[] buildFoldRegions(@NotNull PsiElement root, final @NotNull Document document,
                                                boolean quick) {
        List<FoldingDescriptor> descriptors = new ArrayList<>();
        @SuppressWarnings("unchecked")
        Collection<PsiElement> elements =
                PsiTreeUtil.findChildrenOfAnyType(root, IModuleItem.class, PsiComment.class);
        for (final PsiElement element : elements) {
            final int startOffset = element.getTextRange().getStartOffset();
            final int endOffset = element.getTextRange().getEndOffset();
            final int startLine = document.getLineNumber(startOffset);
            int endLine = document.getLineNumber(endOffset);
            if (element instanceof PsiComment && element.getText().endsWith("\n")) {
                endLine--;
            }
            if (startLine < endLine) {
                if (element instanceof IModuleItem) {
                    TextRange foldingRange = new TextRange(document.getLineEndOffset(startLine), endOffset);
                    descriptors.add(new FoldingDescriptor(element.getNode(), foldingRange,
                            FoldingGroup.newGroup("module item")));
                } else if (element instanceof PsiComment) {
                    descriptors.add(new FoldingDescriptor(element.getNode(), element.getTextRange(),
                            FoldingGroup.newGroup("comment")) {
                        @Nullable
                        @Override
                        public String getPlaceholderText() {
                            return document.getText(new TextRange(startOffset, document.getLineEndOffset(startLine))) +
                                    " ...*/";
                        }
                    });
                }
            }
        }
        return descriptors.toArray(new FoldingDescriptor[descriptors.size()]);
    }

    @Nullable
    @Override
    public String getPlaceholderText(@NotNull ASTNode node) {
        return " ..."; //Used for module item, but not for comment
    }

    @Override
    public boolean isCollapsedByDefault(@NotNull ASTNode node) {
        return node.getPsi() instanceof PsiComment;
    }
}
