package ro.uaic.fmse.kplugin;

import com.intellij.openapi.project.Project;
import com.intellij.openapi.vfs.VirtualFile;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiFile;
import com.intellij.psi.PsiManager;
import com.intellij.psi.search.FileTypeIndex;
import com.intellij.psi.search.GlobalSearchScope;
import com.intellij.psi.util.PsiTreeUtil;
import com.intellij.util.indexing.FileBasedIndex;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import ro.uaic.fmse.kplugin.psi.*;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * @author Denis Bogdanas
 *         Created on 12/11/13.
 */
public class KUtil {

    @NotNull
    public static List<KVarDec> findVarDecsInSameRule(String name, PsiElement element) {
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
    public static KRegularProduction findFirstSyntaxDef(Project project, String name) {
        Collection<VirtualFile> virtualFiles = FileBasedIndex.getInstance().getContainingFiles(FileTypeIndex.NAME,
                KFileType.INSTANCE, GlobalSearchScope.allScope(project));
        for (VirtualFile virtualFile : virtualFiles) {
            KFile kFile = (KFile) PsiManager.getInstance(project).findFile(virtualFile);
            if (kFile != null) {
                Collection<KRegularProduction> syntaxDefs =
                        PsiTreeUtil.findChildrenOfType(kFile, KRegularProduction.class);
                for (KRegularProduction syntaxDef : syntaxDefs) {
                    if (name.equals(syntaxDef.getName())) {
                        return syntaxDef;
                    }
                }
            }
        }
        return null;
    }
}
