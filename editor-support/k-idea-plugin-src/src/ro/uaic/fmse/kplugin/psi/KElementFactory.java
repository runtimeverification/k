// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.psi;

import com.intellij.openapi.project.Project;
import com.intellij.psi.PsiElement;
import com.intellij.psi.PsiFileFactory;
import com.intellij.psi.util.PsiTreeUtil;
import ro.uaic.fmse.kplugin.KFileType;
import ro.uaic.fmse.kplugin.psi.impl.KIdExprBase;

/**
 * @author Denis Bogdanas
 *         Created on 12/14/13.
 */
public class KElementFactory {

    public static KVarDec createVarDec(Project project, String name) {
        String dummyFileContent = String.format("module X rule %1$s:Id => %1$s endmodule", name);
        final KFile file = createFile(project, dummyFileContent);
        //noinspection unchecked
        return PsiTreeUtil.collectElementsOfType(file, KVarDec.class).iterator().next();
    }

    public static KIdExprBase createIdInExpr(Project project, String name) {
        String dummyFileContent = String.format("module X rule %1$s:Id => %1$s endmodule", name);
        final KFile file = createFile(project, dummyFileContent);
        //noinspection unchecked
        return PsiTreeUtil.collectElementsOfType(file, KIdExprBase.class).iterator().next();
    }

    public static KId createId(Project project, String name) {
        String dummyFileContent = String.format("module %1$s rule %1$s:Id => %1$s endmodule", name);
        final KFile file = createFile(project, dummyFileContent);
        return PsiTreeUtil.findChildOfType(file, KId.class);
    }

    public static KSort createSort(Project project, String name) {
        throw new UnsupportedOperationException();
    }

    public static PsiElement createString(Project project, String name) {
        String dummyFileContent = String.format("require \"%1$s\" module %1$s rule %1$s:Id => %1$s endmodule", name);
        final KFile file = createFile(project, dummyFileContent);
        //noinspection ConstantConditions
        return PsiTreeUtil.findChildOfType(file, KStringLiteral.class).getFirstChild();
    }

    public static KFile createFile(Project project, String text) {
        String name = "dummy.k";
        return (KFile) PsiFileFactory.getInstance(project).
                createFileFromText(name, KFileType.INSTANCE, text);
    }
}
