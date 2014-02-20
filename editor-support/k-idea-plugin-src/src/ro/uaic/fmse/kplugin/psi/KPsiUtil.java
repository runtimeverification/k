package ro.uaic.fmse.kplugin.psi;

import com.google.common.base.Predicate;
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

    public static List<KRegularProduction> findSyntaxDefs(Project project, String name) {
        List<KRegularProduction> result = null;
        Collection<VirtualFile> virtualFiles = FileBasedIndex.getInstance().getContainingFiles(FileTypeIndex.NAME,
                KFileType.INSTANCE, GlobalSearchScope.allScope(project));
        for (VirtualFile virtualFile : virtualFiles) {
            KFile kFile = (KFile) PsiManager.getInstance(project).findFile(virtualFile);
            if (kFile != null) {
                Collection<KRegularProduction> syntaxDefs =
                        PsiTreeUtil.findChildrenOfType(kFile, KRegularProduction.class);
                for (KRegularProduction syntaxDef : syntaxDefs) {
                    if (name == null || name.equals(syntaxDef.getName())) {
                        if (result == null) {
                            result = new ArrayList<>();
                        }
                        result.add(syntaxDef);
                    }
                }
            }
        }
        return result != null ? result : Collections.<KRegularProduction>emptyList();
    }

    public static List<KRegularProduction> findSyntaxDefs(Project project) {
        return findSyntaxDefs(project, null);
    }

    @Nullable
    public static <T extends PsiNamedElement> T findFirstElementInModule(KFile refFile, Class<T> elementClass,
                                                                         String... names) {
        final List<String> namesList = Arrays.asList(names);
        Collection<VirtualFile> virtualFiles = getSearchScope(refFile);
        PsiManager psiManager = PsiManager.getInstance(refFile.getProject());
        for (VirtualFile virtualFile : virtualFiles) {
            KFile kFile = (KFile) psiManager.findFile(virtualFile);
            if (kFile != null) {
                T resultCandidate = findFirstElement(kFile, elementClass, new Predicate<T>() {
                    @Override
                    public boolean apply(T t) {
                        return namesList.contains(t.getName());
                    }
                });
                if (resultCandidate != null) {
                    return resultCandidate;
                }
            }
        }
        return null;
    }

    @Nullable
    private static <T extends PsiElement> T findFirstElement(PsiElement rootElement, Class<T> targetClass,
                                                             Predicate<T> predicate) {
        Collection<T> elements = PsiTreeUtil.findChildrenOfType(rootElement, targetClass);
        for (T element : elements) {
            if (predicate == null || predicate.apply(element)) {
                return element;
            }
        }
        return null;
    }

    /**
     * @return the collection pf PSI elements of the given class that satisfy the given predicate.
     */
    @NotNull
    public static <T extends PsiElement> Collection<T> findElementsInModule(PsiElement refElement,
                                                                            Class<T> elementClass,
                                                                            Predicate<T> predicate) {
        Collection<T> result = new ArrayList<>();
        Collection<VirtualFile> virtualFiles = getSearchScope(refElement);
        PsiManager psiManager = PsiManager.getInstance(refElement.getProject());
        for (VirtualFile virtualFile : virtualFiles) {
            KFile kFile = (KFile) psiManager.findFile(virtualFile);
            if (kFile != null) {
                result.addAll(findElements(kFile, elementClass, predicate));
            }
        }
        return result;
    }

    private static <T extends PsiElement> Collection<T> findElements(PsiElement rootElement, Class<T> targetClass,
                                                                     Predicate<T> predicate) {
        Collection<T> elements = PsiTreeUtil.findChildrenOfType(rootElement, targetClass);
        Collection<T> result = new ArrayList<>();
        for (T element : elements) {
            if (predicate.apply(element)) {
                result.add(element);
            }
        }
        return result;
    }

    /**
     * If the file have no "require" clauses and no other files require this one, resolve the reference in the current
     * file scope. Otherwise resolve it in the module scope.
     */
    private static Collection<VirtualFile> getSearchScope(PsiElement element) {
        KFile refFile = (KFile) element.getContainingFile();
        boolean haveRequires = refFile.getRequires().size() > 0;
        Collection<VirtualFile> filesInModule = FileBasedIndex.getInstance().getContainingFiles(FileTypeIndex.NAME,
                KFileType.INSTANCE, getModule(refFile).getModuleContentScope());
        PsiManager psiManager = PsiManager.getInstance(refFile.getProject());
        boolean searchInModule = haveRequires || anyFileRequires(filesInModule, psiManager, refFile.getName());
        return searchInModule
                ? filesInModule
                : Arrays.asList(refFile.getVirtualFile());
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
    public static Collection<KRule> getImplementationRules(KRegularProduction production) {
        final String productionName = production.getName();
        if (productionName == null) {
            return Collections.emptyList();
        }

        Collection<KRule> implRules = findElementsInModule(production, KRule.class, new Predicate<KRule>() {
            @Override
            public boolean apply(KRule kRule) {
                String ruleName = kRule.getRuleName() != null ? kRule.getRuleName().getItemName().getText() : null;

                if (ruleName != null) {
                    int productionNamePos = ruleName.indexOf(productionName);
                    if (productionNamePos != -1) {
                        String productionNamePrefix = ruleName.substring(0, productionNamePos);
                        String productionNameSuffix = ruleName.substring(productionNamePos + productionName.length());
                        if ((productionNamePrefix.equals("") || productionNamePrefix.endsWith("-"))
                                && !productionNamePrefix.endsWith("to-")
                                && (productionNameSuffix.equals("") || productionNameSuffix.startsWith("-"))) {
                            KIdExpr firstIdRefToProductionName =
                                    findFirstElement(kRule.getRuleBody(), KIdExpr.class, new Predicate<KIdExpr>() {
                                        @Override
                                        public boolean apply(KIdExpr kIdExpr) {
                                            return kIdExpr.getText().equals(productionName);
                                        }
                                    });
                            return firstIdRefToProductionName != null;
                        }
                    }
                    return false;
                } else {
                    PsiElement firstChild = kRule.getRuleBody().getFirstChild();
                    return (firstChild instanceof KIdExpr) && firstChild.getText().equals(productionName);
                }
            }
        });

        return implRules;
    }
}
