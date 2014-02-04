package ro.uaic.fmse.kplugin.codeStyle;

import com.intellij.psi.codeStyle.CodeStyleSettings;
import com.intellij.psi.codeStyle.CustomCodeStyleSettings;

/**
 * @author Denis Bogdanas
 *         Created on 4/02/14.
 */
public class KCodeStyleSettings extends CustomCodeStyleSettings {
    public KCodeStyleSettings(CodeStyleSettings settings) {
        super("KCodeStyleSettings", settings);
    }
}
