package ro.uaic.fmse.kplugin.psi;

import com.intellij.extapi.psi.PsiFileBase;
import com.intellij.openapi.fileTypes.FileType;
import com.intellij.psi.FileViewProvider;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.KFileType;
import ro.uaic.fmse.kplugin.KLanguage;

import javax.swing.*;

public class KFile extends PsiFileBase {
  public KFile(@NotNull FileViewProvider viewProvider) {
    super(viewProvider, KLanguage.INSTANCE);
  }

  @NotNull
  @Override
  public FileType getFileType() {
    return KFileType.INSTANCE;
  }

  @Override
  public String toString() {
    return this.getViewProvider().getVirtualFile().getName();
  }

  @Override
  public Icon getIcon(int flags) {
    return super.getIcon(flags);
  }

  @NotNull
  @Override
  public String getName() {
    return this.getViewProvider().getVirtualFile().getNameWithoutExtension();
  }
}
