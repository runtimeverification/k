// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi;

import com.intellij.extapi.psi.PsiFileBase;
import com.intellij.openapi.fileTypes.FileType;
import com.intellij.psi.FileViewProvider;
import com.intellij.psi.util.PsiTreeUtil;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.KFileType;
import ro.uaic.fmse.kplugin.KLanguage;

import javax.swing.*;
import java.util.List;

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

    @NotNull
    public List<KRequire> getRequires() {
        return PsiTreeUtil.getChildrenOfTypeAsList(this, KRequire.class);
    }
}
