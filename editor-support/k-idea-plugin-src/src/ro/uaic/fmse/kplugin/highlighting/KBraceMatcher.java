// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.highlighting;

import com.intellij.lang.BracePair;
import com.intellij.lang.PairedBraceMatcher;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiFile;
import com.intellij.psi.tree.IElementType;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.KIdExpr;
import ro.uaic.fmse.kplugin.psi.KTypes;

/**
 * @author Denis Bogdanas
 *         Created on 12/14/13.
 */
public class KBraceMatcher implements PairedBraceMatcher {
    private static final BracePair[] PAIRS = new BracePair[]{
            new BracePair(KTypes.LEFT_PAREN, KTypes.RIGHT_PAREN, false),
    };

    public BracePair[] getPairs() {
        return PAIRS;
    }

    public boolean isPairedBracesAllowedBeforeType(@NotNull final IElementType lbraceType,
                                                   @Nullable final IElementType tokenType) {
        return true;
    }

    public int getCodeConstructStart(final PsiFile file, int openingBraceOffset) {
        PsiElement element = file.findElementAt(openingBraceOffset);
        if (element == null || element instanceof PsiFile) {
            return openingBraceOffset;
        }
        PsiElement prevSibling = element.getPrevSibling();
        if (prevSibling instanceof KIdExpr) {
            return prevSibling.getTextRange().getStartOffset();
        } else {
            return openingBraceOffset;
        }
    }
}