// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.usages;

import com.intellij.openapi.application.QueryExecutorBase;
import com.intellij.openapi.extensions.Extensions;
import com.intellij.openapi.util.text.StringUtil;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiMethod;
import com.intellij.psi.PsiReference;
import com.intellij.psi.impl.search.CustomPropertyScopeProvider;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.search.SearchRequestCollector;
import com.intellij.psi.search.SearchScope;
import com.intellij.psi.search.UsageSearchContext;
import com.intellij.psi.search.searches.ReferencesSearch;
import com.intellij.psi.util.PropertyUtil;
import com.intellij.util.Processor;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.psi.KSyntax;

/**
 * @author Denis Bogdanas
 *         Created on 19/02/14.
 */
public class KSortPredicateReferenceSearcher extends
        QueryExecutorBase<PsiReference, ReferencesSearch.SearchParameters> {

    public KSortPredicateReferenceSearcher() {
        super(true);
    }

    @Override
    public void processQuery(@NotNull ReferencesSearch.SearchParameters queryParameters, @NotNull
    Processor<PsiReference> consumer) {
        PsiElement refElement = queryParameters.getElementToSearch();
        if (!(refElement instanceof KSyntax)) {
            return;
        }

        addPropertyAccessUsages((KSyntax) refElement, queryParameters.getEffectiveSearchScope(),
                queryParameters.getOptimizer());
    }

    static void addPropertyAccessUsages(KSyntax target, SearchScope scope, SearchRequestCollector collector) {
        final String predicateName = "is" + target.getName();
        if (StringUtil.isNotEmpty(predicateName)) {
            collector.searchWord(predicateName, scope, UsageSearchContext.IN_CODE, true, target);
        }
    }
}
