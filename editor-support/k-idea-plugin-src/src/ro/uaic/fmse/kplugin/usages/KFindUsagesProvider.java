// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.usages;

import com.intellij.lang.cacheBuilder.DefaultWordsScanner;
import com.intellij.lang.cacheBuilder.WordsScanner;
import com.intellij.lang.findUsages.FindUsagesProvider;
import com.intellij.lexer.FlexAdapter;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiNamedElement;
import com.intellij.psi.tree.TokenSet;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.KLexer;
import ro.uaic.fmse.kplugin.psi.*;

import java.io.Reader;

/**
 * @author Denis Bogdanas
 *         Created on 12/14/13.
 */
public class KFindUsagesProvider implements FindUsagesProvider {

    @Nullable
    @Override
    public WordsScanner getWordsScanner() {
        return new DefaultWordsScanner(new FlexAdapter(new KLexer((Reader) null)),
                TokenSet.create(KTypes.KEYWORD, KTypes.BUILTIN_ID, KTypes.BUILTIN_FUNC, KTypes.USER_ID,
                        KTypes.STRING),
                TokenSet.create(KTypes.COMMENT),
                TokenSet.create(KTypes.INTEGER_LITERAL));
    }

    @Override
    public boolean canFindUsagesFor(@NotNull PsiElement psiElement) {
        return psiElement instanceof PsiNamedElement;
    }

    @Nullable
    @Override
    public String getHelpId(@NotNull PsiElement psiElement) {
        return com.intellij.lang.HelpID.FIND_OTHER_USAGES;
    }

    @NotNull
    @Override
    public String getType(@NotNull PsiElement psiElement) {
        if (psiElement instanceof KVarDec) {
            return "Rule Variable";
        } else if (psiElement instanceof KRegularProduction) {
            return "Auxiliary Function";
        } else if (psiElement instanceof KSyntax) {
            return "K Sort";
        } else {
            return "";
        }
    }

    @NotNull
    @Override
    public String getDescriptiveName(@NotNull PsiElement psiElement) {
        return "getDescriptiveName: " + getName(psiElement);
        //return getName(psiElement);
    }

    private String getName(PsiElement psiElement) {
        String name = ((PsiNamedElement) psiElement).getName();
        return name != null ? name : psiElement.getText();
    }

    @NotNull
    @Override
    public String getNodeText(@NotNull PsiElement psiElement, boolean useFullName) {
        return "getNodeText: " + getName(psiElement);
        //return getName(psiElement);
    }
}
