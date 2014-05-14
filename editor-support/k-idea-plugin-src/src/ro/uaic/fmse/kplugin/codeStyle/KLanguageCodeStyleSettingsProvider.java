// Copyright (c) 2014 K Team. All Rights Reserved.
package ro.uaic.fmse.kplugin.codeStyle;

import com.intellij.application.options.IndentOptionsEditor;
import com.intellij.application.options.SmartIndentOptionsEditor;
import com.intellij.lang.Language;
import com.intellij.openapi.diagnostic.Logger;
import com.intellij.openapi.util.io.FileUtil;
import com.intellij.psi.codeStyle.LanguageCodeStyleSettingsProvider;
import org.jetbrains.annotations.NotNull;
import ro.uaic.fmse.kplugin.KLanguage;

import java.io.IOException;

/**
 * @author Denis Bogdanas
 *         Created on 4/02/14.
 */
public class KLanguageCodeStyleSettingsProvider extends LanguageCodeStyleSettingsProvider {
    @NotNull
    @Override
    public Language getLanguage() {
        return KLanguage.INSTANCE;
    }

    @Override
    public IndentOptionsEditor getIndentOptionsEditor() {
        return new SmartIndentOptionsEditor();
    }

    @Override
    public String getCodeSample(@NotNull LanguageCodeStyleSettingsProvider.SettingsType settingsType) {
        try {
            return FileUtil.loadTextAndClose(
                    this.getClass().getResourceAsStream("/ro/uaic/fmse/kplugin/highlighting/KColorSettingsDemo.txt"));
        } catch (IOException e) {
            Logger.getInstance(this.getClass().getName()).error(e);
            return "";
        }
    }
}
