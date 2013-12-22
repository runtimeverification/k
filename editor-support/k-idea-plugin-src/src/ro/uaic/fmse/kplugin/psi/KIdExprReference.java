package ro.uaic.fmse.kplugin.psi;

import com.intellij.openapi.project.Project;
import com.intellij.openapi.util.TextRange;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiElementResolveResult;
import com.intellij.psi.PsiReferenceBase;
import com.intellij.psi.ResolveResult;
import com.intellij.util.IncorrectOperationException;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.KUtil;

import java.util.List;

/**
 * @author Denis Bogdanas
 *         Created on 12/11/13.
 */
public class KIdExprReference extends PsiReferenceBase.Poly<IKIdExprBase> {
    /*Warning: Using multiple reference targets is not recommended.
    */

    private String name;

    public KIdExprReference(@NotNull IKIdExprBase element) {
        super(element, new TextRange(0, element.getTextLength()), true);
        name = element.getText();
    }

    @NotNull
    @Override
    public ResolveResult[] multiResolve(boolean incompleteCode) {
        ResolveResult[] result = resolveRuleVar();
        result = result.length >= 1 ? result : resolveAuxFunctions();
        return result;
    }

    @NotNull
    public ResolveResult[] resolveRuleVar() {
        //The target of a local variable reference is the first typed variable declaration.
        final List<KVarDec> varDecs = KUtil.findVarDecsInSameRule(name, myElement);
        return varDecs.size() >= 1
                ? new ResolveResult[]{new PsiElementResolveResult(varDecs.get(0))}
                : new ResolveResult[0];
    }

    @NotNull
    private ResolveResult[] resolveAuxFunctions() {
        Project project = myElement.getProject();
        KRegularProduction syntaxDef = KUtil.findFirstSyntaxDef(project, name);

        return syntaxDef != null ? new ResolveResult[]{new PsiElementResolveResult(syntaxDef)} : new ResolveResult[0];
    }

    @NotNull
    @Override
    public Object[] getVariants() {
        return new Object[0];
    }

    @Override
    public PsiElement handleElementRename(String newElementName) throws IncorrectOperationException {
        return getElement().setName(newElementName);
    }
}
