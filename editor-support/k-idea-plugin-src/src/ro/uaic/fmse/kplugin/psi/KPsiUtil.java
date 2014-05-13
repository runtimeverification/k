// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi;

import com.google.common.base.Predicate;
import com.intellij.openapi.editor.Document;
import com.intellij.openapi.fileEditor.FileDocumentManager;
import com.intellij.openapi.module.Module;
import com.intellij.openapi.project.Project;
import com.intellij.openapi.roots.ProjectRootManager;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.psi.*;
import com.intellij.psi.search.FileTypeIndex;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.util.indexing.FileBasedIndex;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.KFileType;

import java.util.*;

/**
 * @author Denis Bogdanas
 *         Created on 12/11/13.
 */
public class KPsiUtil {

    @NotNull
    public static List<KVarDec> findVarDecsInSameRule(PsiElement element, String name) {
        KRule rule = getRule(element);
        if (rule != null) {
            return findVarDecs(name, rule);
        } else {
            return Collections.emptyList();
        }
    }

    private static KRule getRule(PsiElement element) {
        while (element != null && !(element instanceof KRule) && !(element instanceof KModule) &&
                !(element instanceof PsiFile)) {
            element = element.getParent();
        }
        return (element instanceof KRule) ? (KRule) element : null;
    }

    @NotNull
    private static List<KVarDec> findVarDecs(String name, KRule rule) {
        List<KVarDec> result = new ArrayList<>();
        @SuppressWarnings("unchecked")
        Collection<KVarDec> typedVars = PsiTreeUtil.collectElementsOfType(rule.getRuleBody(), KVarDec.class);
        for (KVarDec varDec : typedVars) {
            if (varDec.getId() != null && name.equals(varDec.getId().getText())) {
                result.add(varDec);
            }
        }
        return result;
    }

    public static List<PsiNamedElement> findSearchableSymbols(Project project, String name) {
        List<PsiNamedElement> result = new ArrayList<>();
        Collection<VirtualFile> virtualFiles = FileBasedIndex.getInstance().getContainingFiles(FileTypeIndex.NAME,
                KFileType.INSTANCE, GlobalSearchScope.allScope(project));
        for (VirtualFile virtualFile : virtualFiles) {
            KFile kFile = (KFile) PsiManager.getInstance(project).findFile(virtualFile);
            if (kFile != null) {
                @SuppressWarnings("unchecked")
                Collection<PsiNamedElement> syntaxDefs =
                        PsiTreeUtil.findChildrenOfAnyType(kFile, KSyntax.class, KRegularProduction.class);
                List<String> names = new ArrayList<>();
                for (PsiNamedElement syntaxDef : syntaxDefs) {
                    String syntaxDefName = syntaxDef.getName();
                    if ((name == null || name.equals(syntaxDefName)) && !names.contains(syntaxDefName)) {
                        names.add(syntaxDefName);
                        result.add(syntaxDef);
                    }
                }
            }
        }
        return result;
    }

    public static List<PsiNamedElement> findSearchableSymbols(Project project) {
        return findSearchableSymbols(project, null);
    }

    @Nullable
    public static <T extends PsiNamedElement> T findFirstElementInModule(KFile refFile, Class<T> elementClass,
                                                                         String... names) {
        final List<String> namesList = Arrays.asList(names);
        Collection<T> result = findElements(getSearchScope(refFile), elementClass, new Predicate<T>() {
            @Override
            public boolean apply(T t) {
                return namesList.contains(t.getName());
            }
        });
        return !result.isEmpty() ? result.iterator().next() : null;
    }

    @SuppressWarnings("unchecked")
    private static <T extends PsiElement> Collection<T> findElements(Collection<? extends PsiElement> rootElements,
                                                                     Class<? extends T> targetClass,
                                                                     Predicate<T> predicate) {
        Collection<Class<? extends T>> classes = new ArrayList<>();
        classes.add(targetClass);
        return findElements(rootElements, classes, predicate);
    }

    @SuppressWarnings("unchecked")
    private static <T extends PsiElement> Collection<T> findElements(Collection<? extends PsiElement> rootElements,
                                                                     Collection<Class<? extends T>> targetClasses,
                                                                     Predicate<T> predicate) {
        Collection<T> result = new ArrayList<>();
        for (PsiElement rootElement : rootElements) {
            Class<T>[] classes = targetClasses.toArray(new Class[targetClasses.size()]);
            Collection<T> elements = PsiTreeUtil.findChildrenOfAnyType(rootElement, classes);
            for (T element : elements) {
                if (predicate.apply(element)) {
                    result.add(element);
                }
            }
        }
        return result;
    }

    /**
     * If the file have no "require" clauses and no other files require this one, resolve the reference in the current
     * file scope. Otherwise resolve it in the module scope.
     */
    private static Collection<KFile> getSearchScope(PsiElement element) {
        KFile refFile = (KFile) element.getContainingFile();
        boolean haveRequires = refFile.getRequires().size() > 0;
        Collection<VirtualFile> filesInModule = FileBasedIndex.getInstance().getContainingFiles(FileTypeIndex.NAME,
                KFileType.INSTANCE, getModule(refFile).getModuleContentScope());
        PsiManager psiManager = PsiManager.getInstance(refFile.getProject());
        boolean searchInModule = haveRequires || anyFileRequires(filesInModule, psiManager, refFile.getName());
        filesInModule = searchInModule ? filesInModule : Arrays.asList(refFile.getVirtualFile());

        Collection<KFile> result = new ArrayList<>();
        for (VirtualFile virtualFile : filesInModule) {
            KFile kFile = (KFile) psiManager.findFile(virtualFile);
            if (kFile != null) {
                result.add(kFile);
            }
        }
        return result;
    }

    private static boolean anyFileRequires(Collection<VirtualFile> filesInModule, PsiManager psiManager, String name) {
        for (VirtualFile virtualFile : filesInModule) {
            KFile kFile = (KFile) psiManager.findFile(virtualFile);
            if (kFile != null) {
                Collection<KRequire> requireList = PsiTreeUtil.findChildrenOfType(kFile, KRequire.class);
                for (KRequire require : requireList) {
                    if (require.getStringLiteral() != null && require.getStringLiteral().getText().contains(name)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    public static Module getModule(PsiElement element) {
        return ProjectRootManager.getInstance(element.getProject()).getFileIndex()
                .getModuleForFile(element.getContainingFile().getVirtualFile());
    }

    @NotNull
    public static ResolveResult[] resolveAuxFunctions(PsiReference psiReference, String name) {
        KRegularProduction syntaxDef = findFirstElementInModule((KFile) psiReference.getElement().getContainingFile(),
                KRegularProduction.class, name);
        return syntaxDef != null ? new ResolveResult[]{new PsiElementResolveResult(syntaxDef)} : new ResolveResult[0];
    }

    @NotNull
    public static ResolveResult[] resolveLabelDec(PsiReference psiReference, String labelName) {
        List<String> labelDecNames = new ArrayList<>(3);
        labelDecNames.add(labelName);
        String labelWithoutQuote = labelName.substring(1);
        labelDecNames.add(labelWithoutQuote);

        int backQuotePos = labelWithoutQuote.indexOf('`');
        if (backQuotePos != -1) {
            labelDecNames.add(labelWithoutQuote.substring(0, backQuotePos));
        }

        KRegularProduction syntaxDef = findFirstElementInModule((KFile) psiReference.getElement().getContainingFile(),
                KRegularProduction.class, labelDecNames.toArray(new String[labelDecNames.size()]));
        return syntaxDef != null ? new ResolveResult[]{new PsiElementResolveResult(syntaxDef)} : new ResolveResult[0];
    }

    public static ResolveResult[] resolveSyntax(PsiReference psiReference, String sort) {
        KSyntax syntax = findFirstElementInModule((KFile) psiReference.getElement().getContainingFile(), KSyntax.class,
                sort);
        return syntax != null ? new ResolveResult[]{new PsiElementResolveResult(syntax)} : new ResolveResult[0];
    }

    @NotNull
    public static ResolveResult[] resolveRuleVar(PsiReference psiReference, String name) {
        //The target of a local variable reference is the first typed variable declaration.
        final List<KVarDec> varDecs = findVarDecsInSameRule(psiReference.getElement(), name);
        return varDecs.size() >= 1
                ? new ResolveResult[]{new PsiElementResolveResult(varDecs.get(0))}
                : new ResolveResult[0];
    }

    @NotNull
    public static Collection<IModuleItem> getImplementationRulesAndContexts(final KRegularProduction production) {
        String productionName = production.getName();
        if (productionName == null) {
            return Collections.emptyList();
        }
        final String expectedFragmentInRuleName =
                productionName.startsWith("'") ? productionName.substring(1) : productionName;

        List<Class<? extends IModuleItem>> classes = new ArrayList<>();
        classes.add(KRule.class);
        classes.add(KContext.class);

        Collection<IModuleItem> implRules =
                findElements(getSearchScope(production), classes, new Predicate<IModuleItem>() {
                    @Override
                    public boolean apply(IModuleItem moduleItem) {
                        if (moduleItem instanceof KRule) {
                            KRule kRule = (KRule) moduleItem;
                            String ruleName =
                                    kRule.getRuleName() != null ? kRule.getRuleName().getItemName().getText() : null;

                            if (ruleName != null) {
                                int productionNamePos = ruleName.indexOf(expectedFragmentInRuleName);
                                if (productionNamePos != -1) {
                                    String productionNamePrefix = ruleName.substring(0, productionNamePos);
                                    String productionNameSuffix =
                                            ruleName.substring(productionNamePos + expectedFragmentInRuleName.length());
                                    if ((productionNamePrefix.equals("") || productionNamePrefix.endsWith("-"))
                                            && !productionNamePrefix.endsWith("to-")
                                            &&
                                            (productionNameSuffix.equals("") || productionNameSuffix.startsWith("-"))) {
                                        return getReferencesToFast(kRule, production).size() > 0;
                                    }
                                }
                                return false;
                            } else {
                                PsiElement firstChild = kRule.getRuleBody().getFirstChild();
                                return isReferenceToFast(firstChild, production);
                            }
                        } else if (moduleItem instanceof KContext) {
                            return getReferencesToFast(moduleItem, production).size() > 0;
                        }
                        return false;
                    }
                });

        return implRules;
    }

    /**
     * @return The references contained within the given module item to the given production.
     */
    private static Collection<PsiElement> getReferencesToFast(IModuleItem moduleItem,
                                                              final KRegularProduction production) {
        List<Class<? extends PsiElement>> elementClasses = new ArrayList<>();
        elementClasses.add(KIdExpr.class);
        elementClasses.add(KLabel.class);

        return findElements(Arrays.asList(moduleItem), elementClasses, new Predicate<PsiElement>() {
            @Override
            public boolean apply(PsiElement element) {
                return isReferenceToFast(element, production);
            }
        });
    }

    private static boolean isReferenceToFast(PsiElement element, KRegularProduction production) {
        final String productionName = production.getName();
        if (productionName == null) {
            return false;
        }
        //noinspection RedundantCast
        return ((element instanceof KIdExpr) && element.getText().equals(productionName))
                || ((element instanceof KLabel) &&
                element.getText().contains(productionName) &&
                production.equals(((KLabel) element).getReference().resolve()));
    }

    public static Collection<KSyntax> findSyntaxDefs(final KSort sort) {
        return findElements(getSearchScope(sort), KSyntax.class, new Predicate<KSyntax>() {
            @Override
            public boolean apply(KSyntax kSyntax) {
                return kSyntax.getSort().getText().equals(sort.getText());
            }
        });
    }

    /**
     * @return The comment that starts at the same line as the last line of this element, if any.
     */
    public static List<? extends PsiElement> getTrailingSpaceAndComment(PsiElement element) {
        PsiElement next = element.getNextSibling();
        if (next != null) {
            if (next instanceof PsiComment && isTrailingComment(element, (PsiComment) next)) {
                return Arrays.asList(next);
            }
            if (next instanceof PsiWhiteSpace) {
                PsiElement nextNext = next.getNextSibling();
                if (nextNext instanceof PsiComment && isTrailingComment(element, (PsiComment) nextNext)) {
                    return Arrays.asList(next, nextNext);
                }
            }
        }
        return Collections.emptyList();
    }

    private static boolean isTrailingComment(PsiElement element, PsiComment nextComment) {
        Document document = FileDocumentManager.getInstance().getDocument(element.getContainingFile().getVirtualFile());

        return nextComment != null && document != null
                && document.getLineNumber(element.getTextRange().getEndOffset()) ==
                document.getLineNumber(nextComment.getTextOffset());
    }
}
