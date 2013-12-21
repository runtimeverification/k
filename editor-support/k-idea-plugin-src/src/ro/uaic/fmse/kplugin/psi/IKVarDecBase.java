package ro.uaic.fmse.kplugin.psi;

import com.intellij.psi.PsiNameIdentifierOwner;
import org.jetbrains.annotations.Nullable;

/**
 * @author Denis Bogdanas
 *         Created on 12/11/13.
 */
public interface IKVarDecBase extends PsiNameIdentifierOwner {
    @Nullable
    KId getId();
}
